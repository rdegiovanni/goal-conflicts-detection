#!/opt/local/bin/runhugs

import System.Environment
import LTL
import DomGoalsParser
import Tableaux

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Relation as R
import Relation (Relation)

import Debug.Trace

import qualified Model as Model
import Model (Model)

import Conflict

import Data.Time.Clock 

main = do {
	args <- getArgs;
	run_tableaux $ head args
}


run_tableaux = \path -> do {
	start_time <- getCurrentTime;
	str <- readFile path;
	(dom,goals) <- return $ parseDOMandGOALS str;
	spec <- return $ S.union dom goals;
	putStrLn ("Specification Successfully Parsed (" ++ (show (S.size spec)) ++ " formulas).");
	putStr ("Tableaux .. ");
	t <- return $ do_tableaux $ make_tableaux spec;
	print_Tableaux_info t;
	putStrLn ("done.");
	tableau_time <- getCurrentTime;	
	putStrLn $ "Tableau generation time: " ++ show (diffUTCTime tableau_time start_time);
	writeFile "output/tableaux_raw.dot" (tab2dot t);
	
	putStr ("Refining tableaux .. ");
	t2 <- return $ refine_tableaux t;
	print_Tableaux_info t2;
	putStrLn ("done.");
	refinament_time <- getCurrentTime;	
	putStrLn $ "Tableu refinament time: " ++ show (diffUTCTime refinament_time tableau_time);

	if not $ S.null $ nodes t2 then 
		do 	writeFile "output/tableaux.dot" (tab2dot t2)
			run_conflicts_detection path dom goals t2 
	else
		putStrLn ("STRONG conflict detected. The specification is inconsistent.");

	end_time <- getCurrentTime;	
	putStrLn $ "Total Time: " ++ show (diffUTCTime end_time start_time)
}

run_conflicts_detection = \path -> \dom -> \goals -> \t2 -> do {
	conflict_time <- getCurrentTime;

	spec <- return $ S.union dom goals;
	potential_conflict_set <- potential_conflicts spec t2;
	potential_conflict_time <- getCurrentTime;	
	putStrLn $ "Potential Conflicts time: " ++ show (diffUTCTime potential_conflict_time conflict_time);

	if S.null potential_conflict_set then 
			putStrLn ("No WEAK conflict detected.");
	else
		do {
			--putStrLn ("Potential conflicts detected:");
			--putStrLn (show potential_conflict_set);
			putStrLn ("Filtering WEAK conflicts...");
			weak_conflicts_set <- return $ weak_conflicts dom goals potential_conflict_set True;
			--putStrLn (show weak_conflicts_set)
			print_Conflicts_info "ALL" weak_conflicts_set;
			--writeFile (path++"-obtained") (setToString (S.toList weak_conflicts_set))
			filter_conflict_time <- getCurrentTime;	
			putStrLn $ "Filtering Conflicts time: " ++ show (diffUTCTime filter_conflict_time potential_conflict_time) 
		}
}

setToString :: [Formula] -> String
setToString [] = ""
setToString (x:xs) = if (xs == []) then
						(show x) ++ "\n"
					else
						(show x) ++ ";\n" ++ (setToString xs)


print_Tableaux_info = \t -> do {
	size <- return $ S.size (nodes t);
	putStr ("(#nodes= " ++ show (size) ++ ", ");
	putStr ("#trans= " ++ show (R.size (rel t)) ++ ") ")
}


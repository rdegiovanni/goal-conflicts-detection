#!/opt/local/bin/runhugs

import System.Environment
import System.Directory
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

import Control.Monad

main = do {
	args <- getArgs;
	infile <- return $ args!!0 ;
	outfile <- return $ args!!1 ;
	run_tableaux infile outfile
}


run_tableaux = \infile -> \outfile -> do {
	start_time <- getCurrentTime;
	str <- readFile infile;
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
			run_conflicts_detection_fast outfile dom goals t2 
	else
		putStrLn ("STRONG conflict detected. The specification is inconsistent.");

	end_time <- getCurrentTime;	
	putStrLn $ "Total Time: " ++ show (diffUTCTime end_time start_time)
}


run_conflicts_detection = \outfile -> \dom -> \goals -> \t2 -> do {
	conflict_time <- getCurrentTime;

	spec <- return $ S.union dom goals;
	potential_conflict_set <- potential_conflicts spec t2;
	potential_conflict_time <- getCurrentTime;	
	putStrLn $ "Potential Conflicts time: " ++ show (diffUTCTime potential_conflict_time conflict_time);

	if S.null potential_conflict_set then 
			putStrLn ("No WEAK conflict detected.");
	else
		do {
			putStrLn ("Filtering WEAK conflicts...");
			weak_conflicts_set <- return $ weak_conflicts dom goals potential_conflict_set True;
			
			print_Conflicts_info "ALL" weak_conflicts_set;
			
			filter_conflict_time <- getCurrentTime;	
			putStrLn $ "Filtering Conflicts time: " ++ show (diffUTCTime filter_conflict_time potential_conflict_time) 
		}
}

run_conflicts_detection_fast = \outfile -> \dom -> \goals -> \t2 -> do {
	conflict_time <- getCurrentTime;

	spec <- return $ S.union dom goals;
	potential_conflict_set <- potential_conflicts spec t2;
	potential_conflict_time <- getCurrentTime;	
	putStrLn $ "Potential Conflicts time: " ++ show (diffUTCTime potential_conflict_time conflict_time);

	if S.null potential_conflict_set then 
			putStrLn ("No WEAK conflict detected.");
	else
		do {
			dirExists <- doesDirectoryExist outfile ;
			when dirExists	(removeDirectoryRecursive outfile) ;

          	createDirectoryIfMissing True outfile ;
			checks_str <- return $ S.map (allchecks dom goals) potential_conflict_set ;
			writeConflict (outfile++"/C") (S.size checks_str) (S.toList checks_str)
		}
}


print_Tableaux_info = \t -> do {
	size <- return $ S.size (nodes t);
	putStr ("(#nodes= " ++ show (size) ++ ", ");
	putStr ("#trans= " ++ show (R.size (rel t)) ++ ") ")
}

--writeConflict :: String -> Int -> [String]

writeConflict = \fname -> \index -> \str -> do {
	if index == 0 then
		putStrLn ("All the conflicts have been written.")
	else
		do {	
			s <- return $ str!!0 ;
			filename <- return $ (fname++(show index)++".ltl") ;
			writeFile filename  s ;
			xs <- return $ (tail str) ;
			ii <- return $ (index-1) ;
			writeConflict fname ii xs ;
			return ()
		}
}

allchecks :: Set Formula -> Set Formula -> Formula  -> String
allchecks dom goals c = let spec = S.union dom goals;
							combs = S.map (\n -> S.delete n spec) goals ;
							all_combs = S.map (\comb -> (comb S.<+ c)) combs ;
							spec_str = translate (spec S.<+ c) ;
							checks_str = S.map translate all_combs ;
							c_str = translateForm c
						in 
							listToString(c_str:(spec_str:(S.toList checks_str)))






translate :: Set Formula -> String
translate spec = 	if (S.null spec) then
						"True"
					else
						makeFormula $ S.toList (S.map translateForm spec)


makeFormula :: [String] -> String
makeFormula [] = ""
makeFormula [x] = x
makeFormula (x:(y:xs)) = x ++ " & " ++ (makeFormula (y:xs))

translateForm :: Formula -> String
translateForm (And p q) =	"("++translateForm p ++ " & " ++ translateForm q ++")"
translateForm (Or p q) 	=	"("++translateForm p ++ " | " ++ translateForm q ++")"
translateForm (If p q)	=	"("++translateForm p ++ " -> " ++ translateForm q ++")"
translateForm (Iff p q) =	"("++translateForm p ++ " <=> " ++ translateForm q ++")"
--translateForm (Xor p q) =	"("++translateForm p ++ " <=> " ++ translateForm q ++")"
translateForm (Not p)	=	"~" ++ translateForm p
translateForm (U p q) 	=	"(" ++ translateForm p ++ " U " ++ translateForm q ++ ")"
translateForm (W p q) 	=	"( " ++ translateForm (G p) ++ " | " ++ translateForm (U p q) ++ ")"
translateForm (X p) 	=	"X (" ++ translateForm p ++ ")"
translateForm (G p) 	=	"G (" ++ translateForm p ++ ")"
translateForm (F p)		=	"F (" ++ translateForm p ++ ")"
translateForm (Prop s) 	= 	s	
translateForm TrueConst = 	"True"
translateForm FalseConst= 	"False"


listToString :: [String] -> String
listToString [] = ""
listToString (x:xs) = if (xs == []) then
						x ++ "\n"
					else
						x ++ "\n" ++ (listToString xs)


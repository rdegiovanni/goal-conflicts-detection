module Conflict where

import Parser
import LTL
import Closure
import Tableaux as T
import Utils
import BDD as B

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import qualified Data.Map as M
import Data.Map (Map)

import Data.Maybe        (isJust, fromJust, isJust, fromMaybe)

import Data.List	(sortBy, (\\))
import Data.List as L
import Data.Ord


import Debug.Trace

-- Compute WEAK conflicts
-- spec: all formulas that conform the specification.
-- potential_conflicts: potential conflicts computed.
-- returns the seat of portential conflicts that meet with the definition of weak conflicts.
weak_conflicts :: Set Formula -> Set Formula -> Set Formula -> Bool -> Set Formula
weak_conflicts dom goals pot_conflicts cm = 
	let spec = S.union dom goals ;
 		incons_conflicts = S.filter (logical_inconsistency spec) pot_conflicts ;
		min_conflicts 	 = S.filter (if cm then (minimality dom goals) else (domain_consistency dom)) incons_conflicts ;
 		--no_trivials 	 = S.filter (no_trivial_BCs goals) min_conflicts
 	in	
		min_conflicts --no_trivials

-- check logical inconsistency 
logical_inconsistency :: Set Formula -> Formula -> Bool
logical_inconsistency spec pc = not $ isSAT (spec S.<+ pc)

--check minimality
minimality :: Set Formula -> Set Formula -> Formula -> Bool
minimality dom goals ic = 	let spec = S.union dom goals;
								all_comb = S.map (\n -> S.delete n spec) goals
								
						 	in
						 		(trace ".")
						 		S.all (\comb -> isSAT (comb S.<+ ic)) all_comb

-- check logical inconsistency 
domain_consistency :: Set Formula -> Formula -> Bool
domain_consistency dom bc = (trace ".") isSAT (dom S.<+ bc)

no_trivial_BCs :: Set Formula -> Formula -> Bool
no_trivial_BCs goals bc = 	let neg_goals = LTL.negate (make_and (S.toList goals)) ;
							  	neg_bc = LTL.negate bc
							in
								if not $ isSAT (goals S.<+ bc) then 
									isSAT (S.singleton (LTL.And neg_goals neg_bc))
								else
									True

-- Compute potential conflicts
-- potential_conflicts :: Set Formula -> Tableaux -> Set Formula
-- spec: the set of goals and domain properties specified in LTL.
-- t: the tableu generated for spec.
-- returns a set of LTL formulas that potentially characterise goal-conflicts.
potential_conflicts = \spec -> \t -> do {
		reach <- return $ S.filter isF spec;
		putStrLn ("Computing REACH conflicts ...");
		reach_conflicts <- return $ compute_reach_conflicts t reach;
		print_Conflicts_info "REACH" reach_conflicts;

		response <- return $ S.filter (\f -> isGF f || isResponse f) spec;
		putStrLn ("Computing RESPONSE conflicts ...");
		response_conflicts <- return $ compute_response_conflicts t response;
		print_Conflicts_info "RESPONSE" response_conflicts;

		if spec == S.union reach response then
				return (S.union reach_conflicts response_conflicts)
		else
			do{
				putStrLn ("Computing SAFETY conflicts ...");
				safety_conflicts <- return $ compute_safety_conflicts t;
				print_Conflicts_info "SAFE" safety_conflicts;

				return (S.union (S.union reach_conflicts response_conflicts) safety_conflicts)
		}
}


compute_safety_conflicts :: Tableaux ->  Set Formula
compute_safety_conflicts t = 
	let forms = compute_safety_conditions t S.empty [] (root t) 
	in
		S.map make_safety_conflicts forms


compute_reach_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_reach_conflicts t reach = 	
	let tmap = \g -> tagmap t g ;
		frontier_inf = \g -> S.filter (\n -> (fromJust (M.lookup n (tmap g))) == pinf) (nodes t) ;
		live_frontier = \g -> S.filter (\n -> isAnd n && (fromJust (M.lookup n (tmap g))) == 0) (nodes t) ;
		reach_conflict = \g -> (trace (show g ++ " #live-frontier:" ++ show (S.size (live_frontier g)))) 
									 compute_liveness_conditions t (live_frontier g) S.empty [] (root t) ;
		reach_forms = \g -> make_reach_conflicts (make_or $ S.toList $(reach_conflict g)) 
	in
		S.map reach_forms reach

compute_response_conflicts :: Tableaux -> Set Formula -> Set Formula
compute_response_conflicts t pr =	
	let evs = \f -> chopProgress f ;
		response = S.map evs pr ; 
		tmap = \g -> tagmap t g ;
		live_frontier = \g -> S.filter (\n -> isAnd n && (fromJust (M.lookup n (tmap g))) == 0) (nodes t) ;
		response_conflict =  \g -> (trace (show g ++ " #live-frontier:" ++ show (S.size (live_frontier g)))) 
									compute_liveness_conditions t (live_frontier g) S.empty [] (root t) ;
		response_forms = \(If p q) -> make_response_conflicts p q (make_or $ S.toList $ (response_conflict q)) 
	in
		(trace ("response evs: " ++ show response))
		S.map response_forms response


--compute_safety_conditions computes the path conditions to reach the unsatisfiable portion of the tableau.
-- t: tableau generated from the specification.
-- vs: all already visited pre-states (OR nodes).
-- lp: path from the root to the current node.
-- c: current pre-state (OR-node) from which we are going to expand.
compute_safety_conditions :: Tableaux -> Set Node -> [Formula] -> Node -> Set Formula
compute_safety_conditions t vs lp c = 
	let states = succesors t c ;
		--vs' increment visited nodes 
		vs' = S.union vs (S.singleton c) ;
		--compute potential conflicts: path conditions to reach inconsistent nodes.
		local_conflict = condition_to_frontier t lp states 
	in
		--no more PreStates to be expanded
		if (vs' == S.filter isPreState (nodes t)) then
			local_conflict
		else
			--compute successor PreStates, discarding the already visited ones.
			let prestates = (S.unions (S.toList (S.map (succesors t) states) )) S.\\ vs' ;
			--filter States that trasition from PreState c to PreState s.
				filter_states = \s -> (S.intersection states (predecesors t s)) ; 
			--branch condition to force passing through States just filtered.
				in_path = \s -> S.map (branch_condition t) (filter_states s) ;
				out_path = \s -> S.map (branch_condition t) (states S.\\ (filter_states s)) ;
			--generate the formula characterising the step in the path. 	
				in_form = \s -> make_or $ S.toList (in_path s) ;
				out_form = \s -> LTL.negate $ make_or $ S.toList (out_path s) ;
				form = \s -> And (in_form s) (out_form s) ;
			--extend the path to pass this level in the tableau.
				extended_path = \s -> lp ++ [form s] ;
			--compute next level conflicts
				next_level_conflicts = S.map (\s -> compute_safety_conditions t vs' (extended_path s) s) prestates
			in
				--(trace ("next_level_conflicts = " ++ show next_level_conflicts))  
				if (S.null local_conflict) then
					S.unions $ (S.toList next_level_conflicts)
				else
					S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)


-- compute_liveness_conditions computes the path conditions to avoid reaching the states in which the eventualities hold.
-- t: tableau generated from the specification.
-- evNodes: this is a set that contains the nodes in which the eventualities (w.r.t. a liveness goal) hold.
-- vs: all already visited pre-states (OR nodes).
-- lp: path from the root to the current node.
-- c: current pre-state (OR-node) from which we are going to expand.
compute_liveness_conditions :: Tableaux -> Set Node -> Set Node -> [Formula] -> Node -> Set Formula
compute_liveness_conditions t evNodes vs lp c = 
	let states = succesors t c ;
		--vs' increment visited nodes 
		vs' = S.union vs (S.singleton c) ;
		--compute potential conflicts: path conditions to reach inconsistent nodes.
		local_conflict = condition_to_frontier t lp (S.intersection states evNodes)
	in
		--no more PreStates to be expanded
		if (vs' == S.filter isPreState (nodes t)) then
			local_conflict
		else
			--all nodes that don't fulfil the eventuality (i.e., the nodes not contained in live_frontier)
			let states_no_evNodes = states S.\\ evNodes ; 
			--compute successor PreStates, discarding the already visited ones.
				prestates = (S.unions (S.toList (S.map (succesors t) states_no_evNodes) )) S.\\ vs' ;
			--filter States that trasition from PreState c to PreState s.
				filter_states = \s -> (S.intersection states_no_evNodes (predecesors t s)) ; 
			--branch condition to force passing through States just filtered.
				in_path = \s -> S.map (branch_condition t) (filter_states s) ;
				out_path = \s -> S.map (branch_condition t) (states S.\\ (filter_states s)) ;

			--generate the formula characterising the step in the path. 	
				in_form = \s -> make_or $ S.toList (in_path s) ;
				out_form = \s -> LTL.negate $ make_or $ S.toList (out_path s) ;
				form = \s -> And (in_form s) (out_form s) ;

			--extend the path to pass this level in the tableau.
				extended_path = \s -> lp ++ [form s] ;
			--compute next level conflicts
				next_level_conflicts = S.map (\s -> compute_liveness_conditions t evNodes vs' (extended_path s) s) prestates
			in
				if (S.null local_conflict) then
					S.unions $ (S.toList next_level_conflicts)
				else
						S.unions $ [local_conflict] ++ (S.toList next_level_conflicts)


condition_to_frontier :: Tableaux -> [Formula] -> Set Node -> Set Formula
condition_to_frontier t lp conflict_nodes = 
	let incons_paths = 	if S.null conflict_nodes then 
							S.singleton LTL.FalseConst
						else
							S.map (branch_condition t) conflict_nodes ;
		incons_form = LTL.negate $ make_or (S.toList incons_paths) ;
		path_form = buildPathFormula (lp ++ [incons_form])
	in
		if path_form == LTL.FalseConst then
			S.empty
		else
			S.singleton $ path_form
													

--branch condition in one step
branch_condition :: Tableaux -> Node -> Formula
branch_condition t n = make_and $ S.toList $ S.filter isLiteral (formulas n)
						
make_safety_conflicts :: Formula -> Formula
make_safety_conflicts f = (F f)

make_reach_conflicts :: Formula -> Formula
make_reach_conflicts f = (G f)

make_response_conflicts :: Formula -> Formula -> Formula -> Formula
make_response_conflicts p q f = (F (And p (G f)))

buildPathFormula :: [Formula] -> Formula
buildPathFormula [] = LTL.TrueConst
buildPathFormula [x] = B.reduce_formula x
buildPathFormula (x:y:xs) = let x_form = (B.reduce_formula x) ;
								tail_form = buildPathFormula (y:xs)
							in
								if ((x_form == LTL.FalseConst) || (tail_form == LTL.FalseConst)) then
									LTL.FalseConst
								else
									And x_form (X (tail_form))


conflictsToString :: [Formula] -> [String]
conflictsToString [] = []
conflictsToString (x:xs) = (show x):(conflictsToString xs)

print_Conflicts_info = \str -> \bcs -> do {
	putStrLn ("#"++show str ++"-conflicts= " ++ show (S.size bcs) );
	bcs_str <- return $ conflictsToString (S.toList bcs);
	mapM_ putStrLn bcs_str
}




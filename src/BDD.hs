module BDD where

import LTL
import Utils
import Debug.Trace

import qualified Data.Set as S
import Data.Set (Set)
--import qualified SetAux as S
import Data.List	(sortBy, (\\))
import Data.List as L


import Control.Monad.Trans.State.Strict
import Control.Monad
import Data.HBDD.ROBDDFactory
import Data.HBDD.ROBDDContext
import Data.HBDD.ROBDDState
import Data.HBDD.ROBDD as R
import Data.HBDD.Operations as Op hiding (not)

reduce_formula :: Formula -> Formula
reduce_formula f = let (bdd,context) = runState (toBDD f) mkContext in
						robdd_to_formula context bdd					

--this function implements the Shannon expansion from the given BDD.
robdd_to_formula :: ROBDDContext Formula -> ROBDD Formula -> Formula
robdd_to_formula _ Zero                 = LTL.FalseConst
robdd_to_formula _ One                  = LTL.TrueConst
robdd_to_formula c (ROBDD    Zero root Zero _ _) = LTL.FalseConst 	--contradiction
robdd_to_formula c (ROBDD    One root One _ _) = LTL.TrueConst 	--tautology
robdd_to_formula c (ROBDD    One root Zero _ _) = LTL.negate root
robdd_to_formula c (ROBDD    Zero root One _ _) = root
robdd_to_formula c (ROBDD    l root Zero _ _) = LTL.And (LTL.negate root) (robdd_to_formula c l)
robdd_to_formula c (ROBDD    Zero root r _ _) = LTL.And root (robdd_to_formula c r)
robdd_to_formula c (ROBDD    l root One _ _) = LTL.Or root (robdd_to_formula c l) 				-- a&(!a|b)<->a|b
robdd_to_formula c (ROBDD    One root r _ _) = LTL.Or (LTL.negate root) (robdd_to_formula c r)	-- !a&(a|b)<->!a|b
robdd_to_formula c (ROBDD 	 l root r _ _) = LTL.Or (LTL.And (LTL.negate root) (robdd_to_formula c l)) (LTL.And root (robdd_to_formula c r))
robdd_to_formula c (ROBDDRef l root r _ _) = robdd_to_formula c $ lookupUnsafe (ROBDDId l root r) c


toBDD :: Formula -> ROBDDState Formula
toBDD TrueConst = return One
toBDD FalseConst = return Zero
toBDD f@(Prop p)	= singletonC f
toBDD f@(Not p) 	= notC (toBDD p)
toBDD f@(And p q) 	= andC (toBDD p) (toBDD q)
toBDD f@(Or p q) 	= orC (toBDD p) (toBDD q)
toBDD f@(If p q) 	= impC (toBDD p) (toBDD q)
toBDD f@(Iff p q) 	= equivC (toBDD p) (toBDD q)


reduce_CNF_formula :: Set [Formula] -> Formula
reduce_CNF_formula forms = let not_null = S.filter (\l -> not $ L.null l) forms in
							let or_forms = S.map make_or not_null in 
								let and_form = make_and (S.toList or_forms) in
									let red_form = reduce_formula and_form in
										--(trace ("and_form = " ++ (show and_form)))
										--(trace ("red_form = " ++ (show red_form)))
										red_form

reduce_DNF_formula :: Set [Formula] -> Formula
reduce_DNF_formula forms = let not_null = S.filter (\l -> not $ L.null l) forms in
							let and_forms = S.map make_and not_null in 
								let or_form = make_or (S.toList and_forms) in
									reduce_formula or_form




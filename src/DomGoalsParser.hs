module DomGoalsParser where
import Parser
--import ParseLib
import LTL

import qualified Data.Set as S
import Data.Set (Set)
import qualified SetAux as S

import Data.List	(sortBy, (\\))
import Data.List as L

import Data.Maybe as M
import Data.Char as C
import Debug.Trace

--parseFormula :: String -> Formula
--parseFormula s = fst (head (papply pFormula s))

parseDOMandGOALS :: String -> (Set Formula,Set Formula)
parseDOMandGOALS s = let no_comments = (remove_comments s) ;
						 (dom,goals) = split_DOM_and_GOALS no_comments ;
						 dom_forms = if (dom=="") then S.empty else (S.fromList $ parseSpecification dom) ;
						 goals_forms = if (goals=="") then S.empty else (S.fromList $ parseSpecification goals)
					 in
					 	 (dom_forms,goals_forms)


remove_comments :: String -> String
remove_comments s = let splitted = L.lines s in
						let no_comments = L.filter (\l -> not $ L.isPrefixOf "--" l) splitted ;
							add_newline = L.map (\l -> l++"\n") no_comments
						in
							L.foldl (++) ""  add_newline

split_DOM_and_GOALS :: String -> (String,String)
split_DOM_and_GOALS s = let splitted = L.lines s ;
							upper_s = L.map (L.map C.toUpper) splitted ;
							dom_index = L.findIndex (\l -> L.isPrefixOf "DOM" l) upper_s ;
							goal_index = L.findIndex (\l -> L.isPrefixOf "GOAL" l) upper_s	;	
							dom_i = if (M.isJust dom_index) then ((M.fromJust dom_index)+1) else 0 ;
							goal_i = if (M.isJust goal_index) then ((M.fromJust goal_index)+1) else 0 
						in
							if (dom_i < goal_i) then
								let dom_str = if (dom_i==0) then "" else (foldl (++) "" (L.drop dom_i (L.take (goal_i -1) splitted))) ;
									goal_str = if (goal_i==0) then "" else foldl (++) "" (L.drop goal_i splitted)
								in
									--(trace ("dom_i = " ++ show dom_i))
									--(trace ("goal_i = " ++ show goal_i))
									(dom_str,goal_str)
							else
								let dom_str = if (dom_i==0) then "" else (foldl (++) "" (L.drop dom_i splitted)) ;
									goal_str = if (goal_i==0) then "" else (foldl (++) ""  (L.drop goal_i (L.take (dom_i -1) splitted)))
								in
									--(trace ("dom_i = " ++ show dom_i))
									--(trace ("goal_i = " ++ show goal_i))
									(dom_str,goal_str)


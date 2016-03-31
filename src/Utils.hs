module Utils where

import Tableaux
import LTL
import qualified Data.Set as S
import Data.Set (Set)

isSAT :: Set Formula -> Bool
isSAT spec = let t = do_tableaux $ make_tableaux spec ;	
			   	 t2 = refine_tableaux t 
				 in
					S.member (root t2) (nodes t2)


isPreState :: Node -> Bool
isPreState (OrNode _) = True
isPreState _ = False

isTrue :: Formula -> Bool
isTrue TrueConst = True
isTrue _ = False

isFalse :: Formula -> Bool
isFalse FalseConst = True
isFalse _ = False


stateForm :: Formula -> Bool
stateForm TrueConst = True
stateForm FalseConst = True
stateForm (Prop _) = True
stateForm (Not f) = stateForm f
stateForm (And f g) = stateForm f && stateForm g
stateForm (Or f g) = stateForm f && stateForm g
stateForm (If f g) = stateForm f && stateForm g
stateForm (Iff f g) = stateForm f && stateForm g
stateForm _ = False

isF :: Formula -> Bool
isF (U f _) = stateForm f
isF (F _) = True
isF _ = False

isG :: Formula -> Bool
isG (W _ FalseConst) = True
isG (G _) = True
isG _ = False

isGF :: Formula -> Bool
isGF (G f)  = isF f
isGF _ = False

isResponse :: Formula -> Bool
isResponse (G (If f g)) = stateForm f && isF g
isResponse _ = False


chopF :: Formula -> Formula
chopF (U _ f) = f
chopF (F f) = f

chopG :: Formula -> Formula
chopG (W f FalseConst) = f
chopG (G f) = f

chopProgress :: Formula -> Formula
chopProgress g = let f = chopG g in
					if isResponse g then 
						f
					else 
						If TrueConst f



make_and :: [Formula] -> Formula
make_and [] = TrueConst
make_and [x] = x
make_and [x,y] = And x y
make_and (x:y:xs) = let f = make_and xs in
						if isTrue f then
							And x y
						else
							And x (And y f)

make_or :: [Formula] -> Formula
make_or [] = TrueConst
make_or [x] = x
make_or [x,y] = Or x y
make_or (x:y:xs) = let f = make_or xs in
						if isFalse f then
							Or x y
						else
							Or x (Or y f)


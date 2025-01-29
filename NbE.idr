import Data.List

Mult=Nat // For now
Context : Type

data Expr=Var String |
  Pi String Mult Expr Expr |
  Abs String Expr |
  App Expr Expr |
  Sigma String Mult Expr Expr |
  Pair Expr Expr |
  Fst Expr |
  Snd Expr |
  Bool | 
  True |
  False |
  Unit |
  Star
  -- Pair/Unit binding later
  -- Set


get : String -> List String -> Maybe Nat
get sym (x::xs)=if sym==x then Just ((length xs)) else get sym xs
get _ [] = Nothing

αEquivAux : Expr -> Expr -> List String -> List String -> Bool

αEquivAux (Var x) (Var y) map1 map2 = (get x map1) == (get y map2)

αEquivAux (Pi x m1 a1 b1) (Pi y m2 a2 b2) map1 map2 =
  αEquivAux a1 a2 map1 map2
  && let bigger1 = x::map1 in let bigger2 = y::map2 in  αEquivAux b1 b2 bigger1 bigger2
  && m1==m2

αEquivAux (Abs x b1) (Abs y b2) map1 map2 = let bigger1 = x::map1 in let bigger2 = y::map2 in αEquivAux b1 b2 bigger1 bigger2

αEquivAux (Sigma x m1 a1 b1) (Sigma y m2 a2 b2) map1 map2 =
  αEquivAux a1 a2 map1 map2
  && let bigger1 = x::map1 in let bigger2 = y::map2 in  αEquivAux b1 b2 bigger1 bigger2
  && m1 == m2

αEquivAux (Pair a1 b1) (Pair a2 b2) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2

αEquivAux (Fst e1) (Fst e2) map1 map2 = αEquivAux e1 e2 map1 map2
αEquivAux (Snd e1) (Snd e2) map1 map2 = αEquivAux e1 e2 map1 map2
αEquivAux Bool Bool _ _ = True
αEquivAux True True _ _ = True
αEquivAux False False _ _ = True
αEquivAux Unit Unit _ _ = True
αEquivAux Star Star _ _ = True
αEquivAux _ _ _ _ = False

αEquiv : Expr -> Expr -> Bool
αEquiv a b = αEquivAux a b [] [] 

Env : Type

Closure : Type

data Value = VPi Value Closure | VLam Closure | VSigma Value Closure | VPair Value Value | VBool | VFalse | VTrue | VUnit | VStar | VNeu Value Neu
data Neu = NVar String | NApp Neu Norm | Fst Neu | Snd Neu
data Norm = Typed Value Value

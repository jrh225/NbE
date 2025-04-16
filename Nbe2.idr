import Data.List
import Data.Vect
import Data.SortedMap

interface Eq a => Multi a where
  scale : a -> a -> a
  sum : a -> a -> a
  Zero : a
  One : a
  AcceptableZero : a -> Bool
  AcceptableOne : a -> Bool

[Natural] Multi Nat where
  scale n m = n * m 
  sum n m = n + m
  Zero = 0
  One = 1
  AcceptableZero m = m == 0
  AcceptableOne m = m == 1

data IdrisMult = Erase | Linear | Many
Eq IdrisMult where
    Erase  == Erase  = True
    Linear == Linear = True
    Many   == Many   = True
    _ == _ = False


[IdrisRig] Multi IdrisMult where
  scale Erase _ = Erase
  scale _ Erase = Erase
  scale Linear Linear = Linear
  scale _ Many = Many
  scale Many _ = Many

  sum x Erase = x
  sum Erase x = x
  sum Linear Linear = Many
  sum _ Many = Many
  sum Many _ = Many

  Zero = Erase
  One = Linear
  AcceptableZero m = m == Erase || m == Many
  AcceptableOne m = m == Linear || m == Many

[Boolean] Multi Bool where
  scale n m = n && m 
  sum n m = n || m
  Zero = False
  One = True
  AcceptableZero m = not m
  AcceptableOne m = m

[Erasure] Multi Bool where
  scale n m = n && m 
  sum n m = n || m
  Zero = False
  One = True
  AcceptableZero m = True
  AcceptableOne m = m

RangeMult : Type
RangeMult = (Nat,Nat)
[RangeRig] Multi RangeMult where
  scale (a,b) (x,y) = (a*x,b*y) 
  sum (a,b) (x,y) = (a+x,b+y) 
  Zero = (0,0)
  One = (1,1)
  AcceptableZero (a,b) = a==0
  AcceptableOne (a,b) = a<=1 && b>=1

NormalisationError : Type -> Type
NormalisationError = Either String

nextName : String -> String
nextName x = x ++ "'"

freshen : List String -> String -> String
freshen used x = let x=if not (x == "") then x else "x" in if elem x used then freshen used (nextName x) else x

Used : Type -> Type
Used mty = SortedMap String mty
EmptyUsed : (mty:Type) -> Used mty 
EmptyUsed mty = SortedMap.empty 


mutual
  data PreClosure : (mty : Type) -> Multi mty -> Type  where 
    --                          name      body
    MkPreClosure : String -> Pretype mty inter -> PreClosure mty inter

  data Pretype : (mty : Type) -> Multi mty -> Type  where
    --      name      mult    domain          codomain
    Pi    : String -> mty -> Pretype mty inter -> Pretype mty inter -> Pretype mty inter
    --      name      mult    fst          snd
    Sigma : String -> mty -> Pretype mty inter -> Pretype mty inter -> Pretype mty inter 
    Unit  : Pretype mty inter
    Bool  : Pretype mty inter
    El    : Preterm mty inter -> Pretype mty inter
    Set   : Pretype mty inter

  data Preterm : (mty : Type) -> Multi mty -> Type where
    --      name
    Var   : String -> Preterm mty inter
    --      name      mult   domain               body
    Abs   : String -> mty -> Pretype mty inter -> Preterm mty inter -> Preterm mty inter
    --      fn                               arg                              fn type
    App   : Used mty -> Preterm mty inter -> Used mty -> Preterm mty inter -> Pretype mty inter -> Preterm mty inter
    --      fst                              snd         
    Pair  : Used mty -> Preterm mty inter -> Used mty -> Preterm mty inter -> Preterm mty inter
    --      pair                 pair type
    Fst   : Preterm mty inter -> Pretype mty inter -> Preterm mty inter
    --      pair                 pair type
    Snd   : Preterm mty inter -> Pretype mty inter -> Preterm mty inter
    TBool : Preterm mty inter
    True  : Preterm mty inter
    False : Preterm mty inter
    Star  : Preterm mty inter
    Elim  : 
    --      Output type
            PreClosure mty inter ->
    --      true branch
            Used mty -> Preterm mty inter ->
    --      false branch
            Preterm mty inter ->
    --      condition
            Used mty -> Preterm mty inter ->
            Preterm mty inter
    --      name      mult    domain          codomain 
    TPi   : String -> mty -> Preterm mty inter -> Preterm mty inter -> Preterm mty inter
    PLet  : 
    --      Output type
            PreClosure mty inter -> 
    --      fst       snd
            String -> String -> 
    --      pair
            Used mty -> Preterm mty inter -> 
    --      body
            Used mty ->  Preterm mty inter -> 
    --      pair type
            Pretype mty inter -> 
            Preterm mty inter
    ULet  : 
    --      Output type
            PreClosure mty inter -> 
    --      unit
            Used mty -> Preterm mty inter -> 
    --      body
            Used mty ->  Preterm mty inter -> 
            Preterm mty inter

Show mty => Show (Preterm mty inter) where
  show (Var x) = x
  show (Abs x m _ body) = "/" ++ x ++ " : " ++ (show m) ++ "." ++ (show body)
  show (App _ fn _ arg _) = "("++ (show fn) ++ " " ++ (show arg) ++ ")"
  show (Pair _ fst _ snd) = "(" ++ (show fst) ++ ", " ++ (show snd) ++ ")"
  show (Fst pair _) = "Fst " ++ (show pair)
  show (Snd pair _) = "Snd " ++ (show pair)
  show (TBool) = "TBool"
  show (True) = "True"
  show (False) = "False"
  show (Star) = "*"
  show (Elim _ _ t f _ c) = "If " ++ (show c) ++ " Then " ++ (show t) ++ " Else " ++ (show f)
  show (TPi x m d c) = "Pi " ++ (show x) ++ " : (" ++ (show m) ++ ", " ++ (show d) ++ " -> " ++ (show c)
  show (PLet _ fst snd _ pair _ body _) = "Let (" ++ fst ++ ", " ++ snd ++  ") = " ++ (show pair) ++ " in " ++ (show body)
  show (ULet _ _ unit _ body) = "Let * = " ++ (show unit) ++ " in " ++ (show body)




get : String -> List String -> Maybe Nat
get sym (x::xs)=if sym==x then Just ((length xs)) else get sym xs
get _ [] = Nothing

mutual
    TypeαEquivAux : {inter: Multi mty} -> Pretype mty inter -> Pretype mty inter -> List String -> List String -> Bool

    TypeαEquivAux (Pi x m1 a1 b1) (Pi y m2 a2 b2) map1 map2 = TypeαEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in  TypeαEquivAux b1 b2 bigger1 bigger2
      && m1==m2

    TypeαEquivAux (Sigma x m1 a1 b1) (Sigma y m2 a2 b2) map1 map2 =
    TypeαEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in  TypeαEquivAux b1 b2 bigger1 bigger2
      && m1 == m2

    TypeαEquivAux Bool Bool _ _ = True
    TypeαEquivAux Unit Unit _ _ = True
    TypeαEquivAux Set Set _ _ = True
    TypeαEquivAux (El t1) (El t2) _ _ = αEquiv t1 t2 -- Fix
    TypeαEquivAux _ _ _ _ = False

    TypeαEquiv : {inter: Multi mty} -> Pretype mty inter -> Pretype mty inter -> Bool
    TypeαEquiv a b = TypeαEquivAux a b [] []



    αEquivAux : {inter: Multi mty} -> Preterm mty inter -> Preterm mty inter -> List String -> List String -> Bool

    αEquivAux (Var x) (Var y) map1 map2 = case (get x map1, get y map2) of
                                            (Nothing, Nothing) => x==y
                                            (Just a, Just b) => a==b
                                            _ => False

    αEquivAux (Abs x mult1 ty1 b1) (Abs y mult2 ty2 b2) map1 map2 = let bigger1 = x::map1 in let bigger2 = y::map2 in (αEquivAux b1 b2 bigger1 bigger2) && mult1 == mult2 && (TypeαEquivAux ty1 ty2 bigger1 bigger2);
    αEquivAux (App u1 a1 v1 b1 _) (App u2 a2 v2 b2 _) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2 -- u1=u2?

    αEquivAux (Pair u1 a1 v1 b1) (Pair u2 a2 v2 b2) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2 -- u1=u2?

    αEquivAux (Fst e1 _) (Fst e2 _) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux (Snd e1 _) (Snd e2 _) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux TBool TBool _ _ = True
    αEquivAux True True _ _ = True
    αEquivAux False False _ _ = True
    αEquivAux Star Star _ _ = True
    αEquivAux (Elim _ _ t1 f1 _ b1) (Elim _ _ t2 f2 _ b2) map1 map2 = αEquivAux t1 t2 map1 map2 && αEquivAux f1 f2 map1 map2 && αEquivAux b1 b2 map1 map2
    αEquivAux (TPi x m1 a1 b1) (TPi y m2 a2 b2) map1 map2 = αEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in αEquivAux b1 b2 bigger1 bigger2
      && m1==m2

    αEquivAux (PLet _ x1 y1 _ pair1 _ body1 _) ((PLet _ x2 y2 _ pair2 _ body2 _)) map1 map2 = αEquivAux pair1 pair2 map1 map2 && let bigger1 = y1::x1::map1 in let bigger2 = y2::x2::map2 in αEquivAux body1 body2 bigger1 bigger2
    αEquivAux (ULet _ _ unit1 _ body1) ((ULet _ _ unit2 _ body2)) map1 map2 = αEquivAux unit1 unit2 map1 map2 && αEquivAux body1 body2 map1 map2
    αEquivAux _ _ _ _ = False

    αEquiv : {inter: Multi mty} ->  Preterm mty inter -> Preterm mty inter -> Bool
    αEquiv a b = αEquivAux a b [] []

mutual
    Env : (mty : Type) -> Multi mty -> Nat -> Type

    data TypeClosure : (mty : Type) -> Multi mty -> Type where
        MkTypeClosure : {n:Nat} -> Env mty inter n -> String -> TypeValue mty inter -> Pretype mty inter -> TypeClosure mty inter

    data Closure : (mty : Type) -> Multi mty -> Type where
        MkClosure : {n:Nat} -> Env mty inter n -> String -> mty -> TypeValue mty inter -> Preterm mty inter -> Closure mty inter

    data DoubleClosure : (mty : Type) -> Multi mty -> Type where
        MkDoubleClosure : {n:Nat} -> Env mty inter n -> String -> mty -> TypeValue mty inter -> String -> mty -> TypeValue mty inter -> Preterm mty inter -> DoubleClosure mty inter

    data TypeValue : (mty : Type) -> Multi mty -> Type where
      VPi    : mty -> TypeValue mty inter -> TypeClosure mty inter -> TypeValue mty inter
      VSigma : mty -> TypeValue mty inter -> TypeClosure mty inter -> TypeValue mty inter
      VUnit  : TypeValue mty inter
      VBool  : TypeValue mty inter
      VEl    : Value mty inter -> TypeValue mty inter
      VSet   : TypeValue mty inter

    data Value : (mty : Type) -> Multi mty -> Type where
      VAbs   : Closure mty inter -> Value mty inter
      VPair  : Used mty -> Value mty inter -> Used mty -> Value mty inter -> Value mty inter
      VTBool : Value mty inter
      VFalse : Value mty inter
      VTrue  : Value mty inter
      VStar  : Value mty inter
      VNeu   : TypeValue mty inter -> Neu mty inter -> Value mty inter
      VTPi   : mty -> Value mty inter -> Closure mty inter -> Value mty inter

    data Neu : (mty : Type) -> Multi mty -> Type where
      NVar  : String -> Neu mty inter
      NApp  : Used mty -> Neu mty inter -> Used mty -> Norm mty inter -> TypeValue mty inter -> Neu mty inter
      NFst  : Neu mty inter -> TypeValue mty inter -> Neu mty inter
      NSnd  : Neu mty inter -> TypeValue mty inter -> Neu mty inter
      NElim : PreClosure mty inter -> Used mty -> Norm mty inter -> Norm mty inter -> Used mty -> Neu mty inter -> Neu mty inter
      NPLet  :     
      --      Output type
              PreClosure mty inter ->     
      --      fst       snd
              String -> String -> 
      --      pair
              Used mty -> Neu mty inter -> 
      --      body
              Used mty ->  Norm mty inter -> 
      --      pair type
              TypeValue mty inter -> 
              Neu mty inter
      NULet  :     
      --      Output type
              PreClosure mty inter -> 
      --      unit
              Used mty -> Neu mty inter -> 
      --      body
              Used mty ->  Norm mty inter -> 
              Neu mty inter
    
    data Norm : (mty : Type) -> Multi mty -> Type where
      MkNormal : TypeValue mty inter -> Value mty inter -> Norm mty inter
    
doubleClosureName : DoubleClosure mty inter -> (String,String)
doubleClosureName (MkDoubleClosure _ name1 _ _ name2 _ _ _) = (name1,name2)
doubleClosureTy : DoubleClosure mty inter -> (TypeValue mty inter,TypeValue mty inter)
doubleClosureTy (MkDoubleClosure _ _ _ ty1 _ _ ty2 _) = (ty1,ty2)
doubleClosureMult : DoubleClosure mty inter -> (mty,mty)
doubleClosureMult (MkDoubleClosure _ _ m1 _ _ m2 _ _) = (m1,m2)

closureName : Closure mty inter -> String
closureName (MkClosure _ name _ _ _) = name
closureTy : Closure mty inter -> TypeValue mty inter
closureTy (MkClosure _ _ _ ty _) = ty
closureMult : Closure mty inter -> mty
closureMult (MkClosure _ _ m _ _) = m

typeClosureName : TypeClosure mty inter -> String
typeClosureName (MkTypeClosure _ name _ _) = name

Env mty inter n = Vect n (String, mty, Value mty inter, TypeValue mty inter)

zeroEnv : {inter: Multi mty} -> Env mty inter n -> Env mty inter n
zeroEnv [] = []
zeroEnv ((v,m,tm,ty)::env) = ((v,Zero,tm,ty)::(zeroEnv env))

getFresh : {n:Nat} -> Env mty inter n -> String -> String
getFresh env var= freshen ((toList env) <&> fst) var

usedLookup : (Multi mty) => String -> Used mty -> mty
usedLookup v used = case lookup v used of 
                      Just m => m
                      Nothing => Zero

usedIsEmpty : (Multi mty) => Used mty -> Bool
usedIsEmpty used = all (\(_,count) => count == Zero) (Data.SortedMap.toList used)

sumUsed : (Multi mty) => Used mty -> Used mty -> Used mty
sumUsed u1 u2 = mergeWith sum u1 u2

scaleUsed : (Multi mty) => mty -> Used mty -> Used mty
scaleUsed m used = SortedMap.fromList (map (\(v,count) => (v,scale m count)) (Data.SortedMap.toList used))

checkUsed : {inter: Multi mty} -> Env mty inter n -> Used mty -> Bool
checkUsed [] used = usedIsEmpty used
checkUsed ((v,m,_,_)::env) used = m==usedLookup v used && checkUsed env (delete v used)

checkAccept : {inter: Multi mty} -> Env mty inter n -> Bool
checkAccept [] = True
checkAccept ((_,m,_,_)::env) = AcceptableZero m

checkAcceptExcept : {inter: Multi mty} -> Env mty inter n -> String -> Bool
checkAcceptExcept [] var = False
checkAcceptExcept ((v,m,_,_)::env) v2 = if v==v2 then AcceptableOne m && checkAccept env else AcceptableZero m && checkAcceptExcept env v2

take : {inter: Multi mty} -> Env mty inter n -> Used mty -> Env mty inter n
take [] used = []
take ((v,m,val,ty)::env) used = (v,usedLookup v used,val,ty)::(take env (delete v used))

envToUsed : Env mty inter n -> Used mty
envToUsed [] = SortedMap.empty
envToUsed ((v,m,_,_)::env) = SortedMap.insert v m (envToUsed env)

Ctx : (mty : Type) -> Multi mty -> Type
Ctx mty inter = List (String, mty, TypeValue mty inter, Maybe (Value mty inter))

typeLookup : Ctx mty inter -> String -> Maybe (TypeValue mty inter)
typeLookup [] name = Nothing
typeLookup ((x,mult,ty,val)::ctx) y=if x==y then Just ty else typeLookup ctx y
ctxToEnv : Ctx mty inter -> (n:Nat  ** Env mty inter n)
ctxToEnv [] = (0**[])
ctxToEnv ((x,mult,ty,val)::ctx) = let (len ** env) = (ctxToEnv ctx) in (S len**((x, case val of
                                 Just v => (mult,v,ty)
                                 Nothing => (mult,VNeu ty (NVar x),ty)
                             )::env))


data Existence = Exists | Erased

mutual
    TypeValueαEquivAux : {inter: Multi mty} -> TypeValue mty inter -> TypeValue mty inter -> List String -> List String -> NormalisationError Bool
    ValueαEquivAux : {inter: Multi mty} -> Value mty inter -> Value mty inter -> List String -> List String -> NormalisationError Bool
    NeutralαEquivAux : {inter: Multi mty} -> Neu mty inter -> Neu mty inter -> List String -> List String -> NormalisationError Bool

    TypeValueαEquiv : {inter: Multi mty} -> TypeValue mty inter -> TypeValue mty inter -> NormalisationError Bool
    TypeValueαEquiv ty1 ty2 = TypeValueαEquivAux ty1 ty2 [] []
    
    TypeValueαEquivAux (VPi mult1 dom1 cod1) (VPi mult2 dom2 cod2) m1 m2 = let x1 = typeClosureName cod1 in let x2 = typeClosureName cod1 in do 
                                                                          eq_dom <- TypeValueαEquivAux dom1 dom2 m1 m2
                                                                          cod1 <- evalTypeClosure cod1 (VNeu dom1 (NVar x1))
                                                                          cod2 <- evalTypeClosure cod2 (VNeu dom2 (NVar x2))
                                                                          eq_cod <- TypeValueαEquivAux cod1 cod2 (x1::m1) (x2::m2)
                                                                          Right (eq_dom && eq_cod && mult1==mult2)

    TypeValueαEquivAux (VEl (VTPi m dom1 (MkClosure env x _ dom2 cod))) other m1 m2 = TypeValueαEquivAux (VPi m (VEl dom1) (MkTypeClosure env x dom2 (El cod))) other m1 m2
    TypeValueαEquivAux fst  snd@(VEl (VTPi m dom1 (MkClosure env x _ dom2 cod))) m1 m2 = TypeValueαEquivAux snd fst m1 m2

    TypeValueαEquivAux (VSigma mult1 ty_fst1 ty_snd1) (VSigma mult2 ty_fst2 ty_snd2) m1 m2 = let x1 = typeClosureName ty_snd1 in let x2 = typeClosureName ty_snd1 in do 
                                                                          eq_fst <- TypeValueαEquivAux ty_fst1 ty_fst2 m1 m2
                                                                          ty_snd1 <- evalTypeClosure ty_snd1 (VNeu ty_fst1 (NVar x1))
                                                                          ty_snd2 <- evalTypeClosure ty_snd2 (VNeu ty_fst2 (NVar x2))
                                                                          eq_snd <- TypeValueαEquivAux ty_snd1 ty_snd2 (x1::m1) (x2::m2)
                                                                          Right (eq_fst && eq_snd && mult1==mult2)

    TypeValueαEquivAux VBool VBool _ _ = Right True
    TypeValueαEquivAux VBool (VEl VTBool) _ _ = Right True
    TypeValueαEquivAux (VEl VTBool) VBool _ _ = Right True


    TypeValueαEquivAux VUnit VUnit _ _ = Right True

    TypeValueαEquivAux (VEl x) (VEl y) m1 m2 = ValueαEquivAux x y m1 m2

    TypeValueαEquivAux VSet VSet _ _ = Right True

    TypeValueαEquivAux _ _ _ _ = Right False

    ValueαEquivAux (VAbs c1) (VAbs c2) m1 m2 = let x1 = closureName c1 in let x2 = closureName c1 in do 
                                          eq_dom <- TypeValueαEquivAux (closureTy c1) (closureTy c2) m1 m2
                                          b1 <- evalClosure c1 (VNeu (closureTy c1) (NVar x1)) VSet Erased
                                          b2 <- evalClosure c2 (VNeu (closureTy c2) (NVar x2)) VSet Erased
                                          eq_b <- ValueαEquivAux b1 b2 (x1::m1) (x2::m2)
                                          Right (eq_b && (closureMult c1 == closureMult c2) && eq_dom)
    ValueαEquivAux (VPair _ fst1 _ snd1) (VPair _ fst2 _ snd2) m1 m2= do
                                                         eq_fst <- ValueαEquivAux fst1 fst2 m1 m2
                                                         eq_snd <- ValueαEquivAux snd1 snd2 m1 m2
                                                         Right (eq_fst && eq_snd)
    ValueαEquivAux VTBool VTBool _ _ = Right True
    ValueαEquivAux VFalse VFalse _ _ = Right True
    ValueαEquivAux VTrue VTrue _ _ = Right True
    ValueαEquivAux VStar VStar _ _ = Right True
    ValueαEquivAux (VTPi mult1 dom1 cod1) (VTPi mult2 dom2 cod2) m1 m2 = let x1 = closureName cod1 in let x2 = closureName cod1 in do 
                                                                          eq_dom <- ValueαEquivAux dom1 dom2 m1 m2
                                                                          cod1 <- evalClosure cod1 (VNeu (VEl dom1) (NVar x1)) VSet Erased
                                                                          cod2 <- evalClosure cod2 (VNeu (VEl dom2) (NVar x2)) VSet Erased
                                                                          eq_cod <- ValueαEquivAux cod1 cod2 (x1::m1) (x2::m2)
                                                                          Right (eq_dom && eq_cod && mult1==mult2) 

    ValueαEquivAux (VNeu ty1 neu1) (VNeu ty2 neu2) m1 m2 = do 
                                                            eq_ty <- TypeValueαEquivAux ty1 ty2 m1 m2
                                                            eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                            Right (eq_ty && eq_neu)

    ValueαEquivAux _ _ _ _ = Right False


    NeutralαEquivAux (NVar x) (NVar y) m1 m2 = case (get x m1, get y m2) of
                                            (Nothing, Nothing) => Right (x==y)
                                            (Just a, Just b) => Right (a==b)
                                            _ => Right False

    NeutralαEquivAux (NApp _ neu1 _ (MkNormal ty1 val1) _) (NApp _ neu2 _ (MkNormal ty2 val2) _) m1 m2 = do
                                                                                  eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                                                  eq_ty <- TypeValueαEquivAux ty1 ty2 m1 m2
                                                                                  eq_val <- ValueαEquivAux val1 val2 m1 m2
                                                                                  Right (eq_neu && eq_ty && eq_val)
    NeutralαEquivAux (NFst neu1 _) (NFst neu2 _) m1 m2 = NeutralαEquivAux neu1 neu2 m1 m2
    NeutralαEquivAux (NSnd neu1 _) (NSnd neu2 _) m1 m2 = NeutralαEquivAux neu1 neu2 m1 m2
    NeutralαEquivAux (NElim _ _ (MkNormal tty1 tval1) (MkNormal fty1 fval1) _ neu1) (NElim _ _ (MkNormal tty2 tval2) (MkNormal fty2 fval2) _ neu2) m1 m2 = do
                                                                                  eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                                                  eq_tty <- TypeValueαEquivAux tty1 tty2 m1 m2
                                                                                  eq_fty <- TypeValueαEquivAux fty1 fty2 m1 m2
                                                                                  eq_tval <- ValueαEquivAux tval1 tval2 m1 m2
                                                                                  eq_fval <- ValueαEquivAux fval1 fval2 m1 m2
                                                                                  Right (eq_neu && eq_tty && eq_fty && eq_tval && eq_fval)
                                                                                
    NeutralαEquivAux _ _ _ _ = Right False



    eval : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> Preterm mty inter -> TypeValue mty inter -> Existence -> NormalisationError (Value mty inter)

    eval env (Var x) ty existence = evalVar env x ty existence

    eval env (Abs x mult1 ty1 body) (VPi mult2 dom cod) existence = let x'=getFresh env x in let xVal=VNeu dom (NVar x') in do
                                    ty1 <- typeEval (zeroEnv env) ty1
                                    ty_eq <- TypeValueαEquiv dom ty1
                                    output_ty <- evalTypeClosure cod xVal
                                    _ <- evalClosure (MkClosure env x mult1 ty1 body) xVal output_ty existence
                                    if not (mult1 == mult2) then Left "Unequal Multiplicities" else if ty_eq then Right (VAbs (MkClosure env x mult1 ty1 body)) else Left "Unequal Argument Types"

    eval env (Abs x mult1 ty1 body) (VEl (VTPi mult2 dom1 (MkClosure cenv y m (VEl dom2) cod))) existence = eval env (Abs x mult1 ty1 body) (VPi mult2 (VEl dom1) (MkTypeClosure cenv y (VEl dom2) (El cod))) existence

    eval env TBool VSet existence = if checkAccept env then Right VTBool else Left "Under/over used variables1"
    eval env True VBool existence = if checkAccept env then Right VTrue else Left "Under/over used variables2"
    eval env True (VEl VTBool) existence = if checkAccept env then Right VTrue else Left "Under/over used variables3"
    eval env False VBool existence = if checkAccept env then Right VFalse else Left "Under/over used variables4"
    eval env False (VEl VTBool) existence = if checkAccept env then Right VFalse else Left "Under/over used variables5"
    eval env Star VUnit existence = if checkAccept env then Right VStar else Left "Under/over used variables6"

    eval env (App u rator v rand (Pi var mult dom cod)) ty existence = let argExist=if AcceptableZero mult then Erased else existence in do
                            dom <- typeEval (zeroEnv env) dom
                            arg <- eval (take env v) rand dom argExist
                            cod_closure <- Right (MkTypeClosure env var dom cod)
                            fun <- eval (take env u) rator (VPi mult dom cod_closure) existence 
                            output_ty <- evalTypeClosure cod_closure arg
                            ty_eq <- TypeValueαEquiv ty output_ty
                            output <- doApply u fun v arg output_ty existence
                            if not ty_eq then Left "Unequal target types" else if checkUsed env (sumUsed u (scaleUsed mult v)) then Right output else Left "Under/over used variables7"

    eval env (Pair u a v b) (VSigma mult fst_ty snd_ty) existence=  do
                            a <- eval (take env u) a fst_ty existence 
                            snd_ty <- evalTypeClosure snd_ty a
                            b <- eval (take env v) b snd_ty existence 
                            if checkUsed env (sumUsed u v) then Right (VPair u a v b) else Left "Under/over used variables8"

    eval env (Fst pair (Sigma var mult fst_ty snd_ty)) ty Erased=  do -- Fix
                            fst_ty <- typeEval (zeroEnv env) fst_ty
                            snd_ty <- Right (MkTypeClosure env var fst_ty snd_ty)
                            pair <- eval env pair (VSigma mult fst_ty snd_ty) Erased
                            fst <- doFst pair
                            Right fst

    eval env (Fst pair p_ty) ty Exists = Left "Fst used in existing enviroment"

    eval env (Snd pair (Sigma var mult fst_ty snd_ty)) ty Erased= do -- Fix
                            fst_ty <- typeEval (zeroEnv env) fst_ty
                            snd_ty <- Right (MkTypeClosure env var fst_ty snd_ty)
                            pair <- eval env pair (VSigma mult fst_ty snd_ty) Erased
                            snd <- doSnd pair
                            Right snd

    eval env (Snd pair p_ty) ty Exists = Left "Snd used in existing enviroment"

    eval env (Elim st u t f w b) ty existence = do
                            b <- eval (take env w) b VBool existence
                            tty <- evalPreClosure (zeroEnv env) st VTrue VBool
                            fty <- evalPreClosure (zeroEnv env) st VFalse VBool
                            output_ty  <- evalPreClosure (zeroEnv env) st b VBool
                            ty_eq <- TypeValueαEquiv ty output_ty
                            t <- eval (take env u) t tty existence
                            f <- eval (take env u) f tty existence
                            if checkUsed env (sumUsed u w) then if ty_eq then case b of 
                                   VTrue => Right t
                                   VFalse => Right f 
                                   VNeu _ neu => Right (VNeu output_ty (NElim st u (MkNormal tty t) (MkNormal fty f) w neu))
                                   _ => Left "Impossible by b having type bool"
                                else Left "Unequal branch output type" 
                                else Left "Under/over used variables23"
    eval env (TPi x m dom cod) VSet Erased = do
                                 dom <- eval env dom VSet Erased
                                 Right (VTPi m dom (MkClosure env x m (VEl dom) cod)) 
    eval env (PLet st@(MkPreClosure name _) fst snd u pair v body pty@(Sigma var mult fst_ty snd_ty)) ty existence = do
                                                pty <- typeEval (zeroEnv env) pty
                                                pair <- eval (take env u) pair pty existence
                                                gty <- evalPreClosure (zeroEnv env) st (VNeu pty (NVar name)) pty
                                                outputTy <- evalPreClosure (zeroEnv env) st pair pty
                                                eqOut <- TypeValueαEquiv outputTy ty
                                                if eqOut then if checkUsed env (sumUsed u v) then (let sndMult : mty = case existence of
                                                                                                                          Exists => One
                                                                                                                          Erased => Zero
                                                                                                    in let fstMult=scale sndMult mult in  
                                                                     case pair of 
                                                                        (VPair _ v1 _ v2) => do 
                                                                                fst_ty <- typeEval (zeroEnv env) fst_ty
                                                                                snd_ty <- typeEval ((fst,Zero,v1,fst_ty)::(zeroEnv env)) snd_ty
                                                                                output <- eval ((snd,sndMult,v2,snd_ty)::(fst,fstMult,v1,fst_ty)::(take env v)) body outputTy existence
                                                                                Right output
                                                                        (VNeu _ neu) => do
                                                                          fst_ty <- typeEval (zeroEnv env) fst_ty
                                                                          snd_ty <- typeEval ((fst,Zero,(VNeu fst_ty (NVar fst)),fst_ty)::(zeroEnv env)) snd_ty 
                                                                          body <- eval ((snd,sndMult,(VNeu snd_ty (NVar snd)),snd_ty)::(fst,fstMult,(VNeu fst_ty (NVar fst)),fst_ty)::(take env v)) body outputTy existence
                                                                          Right (VNeu outputTy (NPLet st fst snd u neu v (MkNormal outputTy body) pty))
                                                                        _ => Left "Impossible") else Left "Under/over used variables24" else Left "Unequal types when evaluating pair let"
    eval env (ULet st@(MkPreClosure name _) u unit v body) ty existence = do
                                                unit <- eval (take env u) unit VUnit existence
                                                gty <- evalPreClosure (zeroEnv env) st (VNeu VUnit (NVar "x")) VUnit
                                                outputTy <- evalPreClosure (zeroEnv env) st unit VUnit
                                                eqOut <- TypeValueαEquiv outputTy ty
                                                if eqOut then if checkUsed env (sumUsed u v) then (case unit of 
                                                                        VStar => do 
                                                                                output <- eval (take env v) body outputTy existence
                                                                                Right output
                                                                        (VNeu _ neu) => do 
                                                                          body <- eval (take env v) body outputTy existence
                                                                          Right (VNeu outputTy (NULet st u neu v (MkNormal outputTy body)))
                                                                        _ => Left "Impossible") else Left "Under/over used variables24" else Left "Unequal types when evaluating unit let"                                  
                                                


    eval _ _ _ _ = Left "Type has no value of that form"
                            

    evalVar : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> String -> TypeValue mty inter -> Existence -> NormalisationError (Value mty inter)
    evalVar env x ty existence = do
                           i <- case findIndex (\y=> x==fst y) env of 
                                      (Just x) => Right x
                                      Nothing => Left "Variable not in context"
                           eq_ty <- TypeValueαEquiv ty (snd (snd (snd (index i env))))
                           if eq_ty then if case existence of 
                                                                                 Exists => checkAcceptExcept env x 
                                                                                 Erased => checkAccept env
                                                                               then Right (fst (snd (snd (index i env)))) else Left "Under/over used variables9" else Left "Unequal types of variables"
    evalPreClosure : {inter: Multi mty} -> {n:Nat} -> Env mty inter n-> PreClosure mty inter -> Value mty inter -> TypeValue mty inter -> NormalisationError (TypeValue mty inter)
    evalPreClosure env (MkPreClosure x body) val ty = if x=="" then typeEval (zeroEnv env) body else typeEval ((x,Zero,val,ty)::(zeroEnv env)) body

    evalClosure : {inter: Multi mty} -> Closure mty inter -> Value mty inter -> TypeValue mty inter -> Existence -> NormalisationError (Value mty inter)
    evalClosure (MkClosure env x mult ty1 body) v ty2 existence = let mult = case existence of 
                                                                                 Exists => mult 
                                                                                 Erased => Zero
                                                                              in if x=="" then eval env body ty2 existence else eval ((x,mult,v,ty1)::env) body ty2 existence

    evalTypeClosure : {inter: Multi mty} -> TypeClosure mty inter -> Value mty inter -> NormalisationError (TypeValue mty inter)
    evalTypeClosure (MkTypeClosure env x dom cod) v =if x=="" then typeEval (zeroEnv env) cod else typeEval ((x,Zero,v,dom)::(zeroEnv env)) cod


    doApply : {inter: Multi mty} -> Used mty -> Value mty inter -> Used mty -> Value mty inter -> TypeValue mty inter -> Existence -> NormalisationError (Value mty inter)
    doApply _ (VAbs closure) _ arg ty existence = evalClosure closure arg ty existence
    doApply u (VNeu (VPi mult dom cod) neu) v arg ty existence = do
                                              ty2 <- evalTypeClosure cod arg
                                              eq <- TypeValueαEquiv ty ty2
                                              if eq then Right (VNeu ty (NApp u neu v (MkNormal dom arg) (VPi mult dom cod))) else Left "Unequal types between application"
    doApply _ _ _ _ _ _ = Left "Cannot apply something to a non-function"

    doFst : {inter: Multi mty} -> Value mty inter -> NormalisationError (Value mty inter)
    doFst (VPair _ v1 _ v2) = Right v1
    doFst (VNeu (VSigma mult fTy sTy) neu) = Right (VNeu fTy (NFst neu (VSigma mult fTy sTy)) )
    doFst _ = Left "Cannot apply fst to a non-pair"

    doSnd : {inter: Multi mty} -> Value mty inter -> NormalisationError (Value mty inter)
    doSnd (VPair _ v1 _ v2) =Right v2
    doSnd v@(VNeu (VSigma mult fTy sTy) neu) = do
                                             fst <- doFst v
                                             ty <- evalTypeClosure sTy fst
                                             Right (VNeu ty (NSnd neu (VSigma mult fTy sTy)))
    doSnd _ = Left "Cannot apply snd to a non-pair"

    typeEval : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> Pretype mty inter -> NormalisationError (TypeValue mty inter)
    typeEval env (Pi name mult dom cod) = do
                                            dom <- typeEval env dom
                                            Right (VPi mult dom (MkTypeClosure env name dom cod))
    typeEval env (Sigma name mult fTy sTy) = do
                                            fTy <- typeEval env fTy
                                            Right (VSigma mult fTy (MkTypeClosure env name fTy sTy))

    typeEval env Unit = if checkAccept env then Right (VUnit) else Left "Under/over used variables10"
    typeEval env Bool = if checkAccept env then Right (VBool) else Left "Under/over used variables11"
    typeEval env Set = if checkAccept env then Right (VSet) else Left "Under/over used variables12"
    typeEval env (El expr) = do
                                     expr <- eval env expr VSet Erased
                                     Right (VEl expr)

    readBackTypeNormal : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> TypeValue mty inter -> NormalisationError (Pretype mty inter)
    readBackTypeNormal env (VPi mult dom cod) = let x=getFresh env (typeClosureName cod) in let xVal=VNeu dom (NVar x) in do
                                                pre_dom <- readBackTypeNormal env dom
                                                ty_val_cod <- evalTypeClosure cod xVal
                                                pre_cod <- readBackTypeNormal ((x,Zero,xVal,dom)::env) ty_val_cod
                                                Right (Pi x mult pre_dom pre_cod)
    readBackTypeNormal env (VSigma mult dom cod) = let x=getFresh env (typeClosureName cod) in let xVal=VNeu dom (NVar x) in do
                                                pre_dom <- readBackTypeNormal env dom
                                                ty_val_cod <- evalTypeClosure cod xVal
                                                pre_cod <- readBackTypeNormal ((x,Zero,xVal,dom)::env) ty_val_cod
                                                Right (Sigma x mult pre_dom pre_cod)
    readBackTypeNormal env VBool = if checkAccept env then Right Bool else Left "Under/over used variables13"
    readBackTypeNormal env VUnit =if checkAccept env then Right Unit else Left "Under/over used variables14"
    readBackTypeNormal env VSet = if checkAccept env then Right Set else Left "Under/over used variables15"
    readBackTypeNormal env (VEl val) = do
                                      val <- readBackNormal env VSet val Erased
                                      Right (El val)

    readBackNormal : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> TypeValue mty inter -> Value mty inter -> Existence -> NormalisationError (Preterm mty inter)
    readBackNeutral : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> Neu mty inter -> Existence -> NormalisationError (Preterm mty inter)

    readBackNormal env (VPi mult dom cod) fun existence = let mult' = case existence of 
                                                                                 Exists => mult 
                                                                                 Erased => Zero
                                                                              in let x = getFresh env(typeClosureName cod) in let xVal = VNeu dom (NVar x) in do
                                                  cod <- evalTypeClosure cod xVal
                                                  body <- doApply (envToUsed env) fun (SortedMap.fromList [(x,One)]) xVal cod existence
                                                  body <- readBackNormal ((x,mult',xVal,dom)::env) cod body existence
                                                  dom <- readBackTypeNormal (zeroEnv env) dom
                                                  Right (Abs x mult dom body)



    readBackNormal env (VSigma mult fTy sTy) pair Erased= do
                                                  fst <- doFst pair
                                                  snd <- doSnd pair

                                                  sTy <- evalTypeClosure sTy fst

                                                  fst <- readBackNormal env fTy fst Erased
                                                  snd <- readBackNormal env sTy snd Erased
                                                  Right (Pair SortedMap.empty fst SortedMap.empty snd)


    readBackNormal env VUnit _ Erased =if checkAccept env then Right Star else Left "Under/over used variables16"
    readBackNormal env t (VNeu t′ neu) existence= readBackNeutral env neu existence

    readBackNormal env (VSigma mult fTy sTy) (VPair u fst v snd) Exists= do

                                              sTy <- evalTypeClosure sTy fst

                                              fst <- readBackNormal env fTy fst Erased
                                              snd <- readBackNormal env sTy snd Erased
                                              Right (Pair u fst v snd)

    readBackNormal env (VSigma mult fTy sTy) _ _ = Left "Type has no value of this form"
    readBackNormal env VBool VFalse _ = if checkAccept env then Right False else Left "Under/over used variables17"
    readBackNormal env VBool VTrue _ = if checkAccept env then Right True else Left "Under/over used variables18"
    readBackNormal env VBool _ _ = Left "Type has no value of this form"

    readBackNormal env VUnit VStar _ = if checkAccept env then Right Star else Left "Under/over used variables19"
    readBackNormal env VUnit _ _= Left "Type has no value of this form"

    readBackNormal env VSet VTBool _ = if checkAccept env then Right TBool else Left "Under/over used variables20"
    readBackNormal env VSet _  _= Left "Type has no value of this form"

    readBackNormal env (VEl VTBool) VFalse _ = if checkAccept env then Right False else Left "Under/over used variables21"
    readBackNormal env (VEl VTBool) VTrue _ = if checkAccept env then Right False else Left "Under/over used variables22"

    readBackNormal env (VEl (VTPi mult dom (MkClosure cenv y m (VEl dom2) cod))) fun existence = readBackNormal env (VPi mult (VEl dom) (MkTypeClosure cenv y (VEl dom2) (El cod))) fun existence 
    readBackNormal env (VEl _) _ _= Left "Type has no value of this form"

    readBackNeutral env (NVar x) _ = Right (Var x)
    readBackNeutral env (NApp u neu v (MkNormal ty arg) ty2) existence = do -- Check type again?
                                            fun <- readBackNeutral env neu existence
                                            arg <- readBackNormal env ty arg existence
                                            ty2 <- readBackTypeNormal (zeroEnv env) ty2
                                            Right (App u fun v arg ty2)
    readBackNeutral env (NFst neu ty)  Erased = do
                                         pair <- readBackNeutral env neu Erased
                                         ty <- readBackTypeNormal (zeroEnv env) ty
                                         Right (Fst pair ty)
    readBackNeutral env (NSnd neu ty) Erased = do
                                         pair <- readBackNeutral env neu Erased
                                         ty <- readBackTypeNormal (zeroEnv env) ty
                                         Right (Snd pair ty)
    readBackNeutral env (NFst neu ty) Exists = Left "Fst used in existing enviroment"
    readBackNeutral env (NSnd neu ty) Exists = Left "Snd used in existing enviroment"

    readBackNeutral env (NElim st u (MkNormal tty t) (MkNormal fty f) w b) existence=do 
                                                                                       t <- readBackNormal (take env u) tty t existence
                                                                                       f <- readBackNormal (take env u) fty f existence
                                                                                       b <- readBackNeutral (take env w) b existence
                                                                                       Right (Elim st u t f w b)
    
    readBackNeutral env (NPLet st fst snd u pair v (MkNormal ty body) pty) existence = do
      pair <- readBackNeutral (take env u) pair existence
      body <- readBackNormal (take env v) ty body existence --fix
      pty <- readBackTypeNormal (zeroEnv env) pty
      Right (PLet st fst snd u pair v body pty)

    readBackNeutral env (NULet st u unit v (MkNormal ty body)) existence = do
      unit <- readBackNeutral (take env u) unit existence
      body <- readBackNormal (take env v) ty body existence
      Right (ULet st u unit v body)
      
    

    norm : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> Preterm mty inter-> Pretype mty inter-> Existence -> NormalisationError (Preterm mty inter)
    norm env expr ty existence = do
                    ty <- case typeEval (zeroEnv env) ty of 
                      Left error => Left ("Given Type Error: " ++ error)
                      Right v => Right v
                    value <- eval env expr ty existence
                    case readBackNormal env ty value existence of 
                      Left error => Left ("Impossible: " ++ error)
                      Right v => Right v
    debugValue : {inter: Multi mty} -> {n:Nat} -> Env mty inter n -> Preterm mty inter-> Pretype mty inter-> Existence -> NormalisationError (Value mty inter)
    debugValue env expr ty existence =do
                    ty <- case typeEval (zeroEnv env) ty of 
                      Left error => Left ("Given Type Error: " ++ error)
                      Right v => Right v
                    eval env expr ty existence


fnType:  String -> mty -> Pretype mty inter -> Pretype mty inter -> Pretype mty inter
fnType v mult x y= Pi v mult x y

pairType:  String -> mty -> Pretype mty inter -> Pretype mty inter -> Pretype mty inter
pairType v mult x y= Sigma v mult x y


typeVar : String -> Pretype mty inter
typeVar v = El (Var v)


-- Examples
example_unit_fn : Either String (Preterm Nat Natural)
example_unit_fn = norm [] (Abs "x" 1 Unit (Var "x")) (fnType "x" 1 Unit Unit) Exists

example_wrong_mult1 : Either String (Preterm Nat Natural)
example_wrong_mult1 = norm [] (Abs "x" 1 Unit (Var "x")) (fnType "x" 2 Unit Unit) Exists

example_wrong_mult2 : Either String (Preterm Nat Natural)
example_wrong_mult2 = norm [] (Abs "x" 2 Unit (Var "x")) (fnType "x" 1 Unit Unit) Exists

example_erased_eta : Either String (Preterm Nat Natural)
example_erased_eta = norm [] (Abs "y" 1 Unit (Var "y")) (fnType "y" 1 Unit Unit) Erased

singleCtx : Ctx Nat Natural 
singleCtx = [("T",0,VSet,Nothing)]
example3 : Either String (Preterm Nat Natural)
example3 = let (n ** env)=ctxToEnv singleCtx in norm env (Abs "x" 1 (typeVar "T") (Var "x")) (fnType "x" 1 (typeVar "T")  (typeVar "T") ) Exists

boolCtx : Ctx Nat Natural 
boolCtx = [("b",1,VBool,Nothing)]
example4 : Either String (Preterm Nat Natural)
example4 = let (n ** env)=ctxToEnv boolCtx in norm env (Elim (MkPreClosure "b" Bool) (EmptyUsed Nat) True False (SortedMap.fromList [("b",1)]) (Var "b")) Bool Exists

fCtx : Ctx Nat Natural
fCtx=[("f",0,(VPi 10 VUnit (MkTypeClosure [] "x" VUnit Bool)),Nothing)]
term6 : Preterm Nat Natural
term6 = (Var "f")
example6 = let (n ** env)=ctxToEnv fCtx in norm env term6 (fnType "x" 10 Unit Bool) Erased

term7 : Preterm Bool Boolean
term7 = (Abs "x" True Unit (Pair (SortedMap.fromList [("x",True)]) (Var "x") (SortedMap.fromList [("x",True)]) (Var "x")))
example7 = norm [] term7 (fnType "x" True Unit (pairType "x" True Unit Unit)) Exists

term8 : Preterm RangeMult RangeRig
term8 = (Abs "x" (0,1) Unit (Var "x"))
example8 = norm [] term8 (fnType "x" (0,1) Unit Unit) Exists

term9 : Preterm RangeMult RangeRig
term9 = (Abs "x" (0,1) Unit Star)
example9 = norm [] term9 (fnType "x" (0,1) Unit Unit) Exists

ranCtx : Ctx RangeMult RangeRig 
ranCtx=[("b",(0,2),VUnit,Nothing)]
term10 = (App (EmptyUsed RangeMult) (Abs "x" (0,1) Unit (Var "x")) (SortedMap.fromList [("b", (0,2))]) (Var "b") (fnType "x" (0,1) Unit Unit))
example10 = let (n ** env)=ctxToEnv ranCtx in norm env term10 Unit Exists

term11 : Preterm Nat Natural
term11 = (PLet (MkPreClosure "x" Unit) "x" "y" (EmptyUsed Nat) (Pair (EmptyUsed Nat)  Star (EmptyUsed Nat)  Star) (EmptyUsed Nat)  (Var "y") (Sigma "x" 0 Unit Unit))
example11 = norm [] term11 Unit Exists

unitCtx : Ctx Nat Natural 
unitCtx=[("x",1,VUnit,Nothing)]
term12 = (ULet (MkPreClosure "x" Unit) (SortedMap.fromList [("x",1)]) (Var "x") (EmptyUsed Nat) (Star))
example12 = let (n ** env)=ctxToEnv unitCtx in norm env term12 Unit Exists

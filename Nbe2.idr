import Data.List

Mult=Nat --For now

nextName : String -> String
nextName x = x ++ "'"

freshen : List String -> String -> String
freshen used x = if elem x used then freshen used (nextName x) else x


mutual
  data Pretype=Pi String Mult Pretype Pretype |
    Sigma String Mult Pretype Pretype |
    Unit |
    Bool |
    El Preterm |
    Set

  data Preterm=Var String |
    Abs String Mult Pretype Preterm |
    App Preterm Preterm |
    Pair Preterm Preterm |
    Fst Preterm |
    Snd Preterm |
    TBool |
    True |
    False |
    Star
  -- Pair/Unit binding later
  -- Elim later
  -- dependent function type?

get : String -> List String -> Maybe Nat
get sym (x::xs)=if sym==x then Just ((length xs)) else get sym xs
get _ [] = Nothing

mutual
    TypeαEquivAux : Pretype -> Pretype -> List String -> List String -> Bool

    TypeαEquivAux (Pi x m1 a1 b1) (Pi y m2 a2 b2) map1 map2 =
    TypeαEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in  TypeαEquivAux b1 b2 bigger1 bigger2
      && m1==m2

    TypeαEquivAux (Sigma x m1 a1 b1) (Sigma y m2 a2 b2) map1 map2 =
    TypeαEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in  TypeαEquivAux b1 b2 bigger1 bigger2
      && m1 == m2

    TypeαEquivAux Bool Bool _ _ = True
    TypeαEquivAux Unit Unit _ _ = True
    TypeαEquivAux Set Set _ _ = True
    TypeαEquivAux (El t1) (El t2) _ _ = αEquiv t1 t2
    TypeαEquivAux _ _ _ _ = False

    TypeαEquiv : Pretype -> Pretype -> Bool
    TypeαEquiv a b = TypeαEquivAux a b [] []



    αEquivAux : Preterm -> Preterm -> List String -> List String -> Bool

    αEquivAux (Var x) (Var y) map1 map2 = case (get x map1, get y map2) of
                                            (Nothing, Nothing) => x==y
                                            (Just a, Just b) => a==b
                                            _ => False

    αEquivAux (Abs x mult1 ty1 b1) (Abs y mult2 ty2 b2) map1 map2 = let bigger1 = x::map1 in let bigger2 = y::map2 in (αEquivAux b1 b2 bigger1 bigger2) && mult1==mult2 && (TypeαEquivAux ty1 ty2 bigger1 bigger2);
    αEquivAux (App a1 b1) (App a2 b2) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2

    αEquivAux (Pair a1 b1) (Pair a2 b2) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2

    αEquivAux (Fst e1) (Fst e2) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux (Snd e1) (Snd e2) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux TBool TBool _ _ = True
    αEquivAux True True _ _ = True
    αEquivAux False False _ _ = True
    αEquivAux Star Star _ _ = True
    αEquivAux _ _ _ _ = False

    αEquiv : Preterm -> Preterm -> Bool
    αEquiv a b = αEquivAux a b [] []



-- Merge all of this?
mutual
    Env : Type

    data TypeClosure = MkTypeClosure Env String Pretype
    data Closure = MkClosure Env String Mult TypeValue Preterm

    data TypeValue = VPi Mult TypeValue TypeClosure | VSigma Mult TypeValue TypeClosure | VBool | VUnit | VEl Value | VSet

    data Value = VAbs Closure | VPair Value Value | VTBool | VFalse | VTrue | VStar | VNeu TypeValue Neu
    data Neu = NVar String | NApp Neu Norm | NFst Neu | NSnd Neu
    data Norm = MkNormal TypeValue Value


closureName : Closure -> String
closureName (MkClosure _ name _ _ _) = name
typeClosureName : TypeClosure -> String
typeClosureName (MkTypeClosure _ name _) = name


Env = List  (String, Mult, Value)

data CtxEntry = Defintion  Value | Unknown TypeValue
Ctx=List (String, Mult, TypeValue, Maybe Value)

typeLookup : Ctx -> String -> Maybe TypeValue
typeLookup [] name = Nothing
typeLookup ((x,mult,ty,val)::ctx) y=if x==y then Just ty else typeLookup ctx y
ctxToEnv : Ctx -> Env
ctxToEnv [] = []
ctxToEnv ((x,mult,ty,val)::ctx) = ((x, case val of
                                 Just v => (mult,v)
                                 Nothing => (mult,VNeu ty (NVar x))
                             )::(ctxToEnv ctx))




mutual
    eval : Env -> Preterm -> Maybe Value


    eval env (Var x) = evalVar env x
    eval env (Abs x mult ty body) = do
                                    ty <- typeEval env ty
                                    (Just (VAbs (MkClosure env x mult ty body)))
    eval env TBool = Just VTBool
    eval env True = Just VTrue
    eval env False = Just VFalse
    eval env Star = Just VStar

    eval env (App rator rand) = do
                            fun <- eval env rator
                            arg <- eval env rand
                            doApply fun arg

    eval env (Pair a b) = do
                            a <- eval env a
                            b <- eval env b
                            Just (VPair a b)

    eval env (Fst pair) = do
                            pair <- eval env pair
                            doFst pair

    eval env (Snd pair) = do
                            pair <- eval env pair
                            doSnd pair


    evalVar : Env -> String -> Maybe Value
    evalVar [] x = Nothing
    evalVar ((y, mult, val) :: env) x = if x==y then Just val else evalVar env x

    evalClosure : Closure -> Value -> Maybe Value
    evalClosure (MkClosure env x mult ty body) v = eval ((x,mult,v)::env) body

    evalTypeClosure : TypeClosure -> Value -> Maybe TypeValue
    evalTypeClosure (MkTypeClosure env x e) v = typeEval ((x,0,v)::env) e


    doApply : Value -> Value -> Maybe Value
    doApply (VAbs closure) arg = evalClosure closure arg
    doApply (VNeu (VPi mult dom cod) neu) arg = do
                                              ty <-evalTypeClosure cod arg
                                              Just (VNeu ty (NApp neu (MkNormal dom arg)))
    doApply _ _ = Nothing

    doFst : Value -> Maybe Value
    doFst (VPair v1 v2) = Just v1
    doFst (VNeu (VSigma mult fTy sTy) neu) = Just (VNeu fTy (NFst neu))
    doFst _ = Nothing

    doSnd : Value -> Maybe Value
    doSnd (VPair v1 v2) =Just v2
    doSnd v@(VNeu (VSigma mult fTy sTy) neu) = do
                                             dom <- doFst v
                                             ty <- evalTypeClosure sTy dom
                                             Just (VNeu ty (NSnd neu))
    doSnd _ = Nothing

    typeEval : Env -> Pretype -> Maybe TypeValue
    typeEval env (Pi name mult dom cod) = do
                                            dom <- typeEval env dom
                                            Just (VPi mult dom (MkTypeClosure env name cod))
    typeEval env (Sigma name mult fTy sTy) = do
                                            fTy <- typeEval env fTy
                                            Just (VSigma mult fTy (MkTypeClosure env name sTy))

    typeEval env Unit = Just (VUnit)
    typeEval env Bool = Just (VBool)
    typeEval env Set = Just (VSet)
    typeEval env (El expr) = do
                                     expr <- eval env expr
                                     Just (VEl expr)

mutual
    readBackTypeNormal : Ctx -> TypeValue -> Maybe Pretype
    readBackTypeNormal ctx (VPi mult dom cod) = let x=freshen (map fst ctx) (typeClosureName cod) in do
                                                pre_dom <- readBackTypeNormal ctx dom
                                                ty_val_cod <- evalTypeClosure cod (VNeu dom (NVar x))
                                                pre_cod <- readBackTypeNormal ((x,0,dom,Nothing)::ctx) ty_val_cod
                                                Just (Pi x mult pre_dom pre_cod)
    readBackTypeNormal ctx (VSigma mult dom cod) = let x=freshen (map fst ctx) (typeClosureName cod) in do
                                                pre_dom <- readBackTypeNormal ctx dom
                                                ty_val_cod <- evalTypeClosure cod (VNeu dom (NVar x))
                                                pre_cod <- readBackTypeNormal ((x,0,dom,Nothing)::ctx) ty_val_cod
                                                Just (Sigma x mult pre_dom pre_cod)
    readBackTypeNormal ctx VBool = Just Bool
    readBackTypeNormal ctx VUnit = Just Unit
    readBackTypeNormal ctx VSet = Just Set
    readBackTypeNormal ctx (VEl val) = do
                                      val <- readBackNormal ctx VSet val
                                      Just (El val)

    readBackNormal : Ctx -> TypeValue -> Value -> Maybe Preterm
    readBackNeutral : Ctx -> Neu -> Maybe Preterm

    readBackNormal ctx (VPi mult dom cod) fun = let x = freshen (map fst ctx) (typeClosureName cod) in let xVal = VNeu dom (NVar x) in do
                                                  ty <- evalTypeClosure cod xVal
                                                  body <- doApply fun (VNeu dom (NVar x))
                                                  body <- readBackNormal ((x,mult,ty,Nothing)::ctx) ty body
                                                  dom <- readBackTypeNormal ctx dom
                                                  Just (Abs x mult dom body)



    readBackNormal ctx (VSigma mult fTy sTy) pair = do
                                                  fst <- doFst pair
                                                  snd <- doSnd pair

                                                  sTy <- evalTypeClosure sTy fst

                                                  fst <- readBackNormal ctx fTy fst
                                                  snd <- readBackNormal ctx sTy snd
                                                  Just (Pair fst snd)

    readBackNormal ctx t (VNeu t′ neu) = readBackNeutral ctx neu -- t==t'?
    readBackNormal ctx VBool VFalse = Just False
    readBackNormal ctx VBool VTrue = Just True
    readBackNormal ctx VBool _ = Nothing

    readBackNormal ctx VUnit VStar = Just Star
    readBackNormal ctx VUnit _ = Nothing

    readBackNormal ctx VSet VTBool = Just TBool
    readBackNormal ctx VSet _ = Nothing

    readBackNormal ctx (VEl VTBool) VFalse = Just False
    readBackNormal ctx (VEl VTBool) VTrue = Just False

    -- readBackNormal ctx (VEl (VNeu VSet (NVar name))) value = ctx x:T f:T->T
    -- expr VNeu T NApp f (VNeu T x)
    -- VEl (VNeu VSet (NVar "T"))

    readBackNormal ctx (VEl _) _ = Nothing

    readBackNeutral ctx (NVar x) = Just (Var x)
    readBackNeutral ctx (NApp neu (MkNormal ty arg)) = do
                                            fun <- readBackNeutral ctx neu
                                            arg <- readBackNormal ctx ty arg
                                            Just (App fun arg)
    readBackNeutral ctx (NFst neu) = do
                                         pair <- readBackNeutral ctx neu
                                         Just (Fst pair)
    readBackNeutral ctx (NSnd neu) = do
                                         pair <- readBackNeutral ctx neu
                                         Just (Snd pair)


norm : Env -> Preterm -> Pretype -> Maybe Preterm
norm env expr ty = do
                  ty <- typeEval env ty
                  value <- eval env expr
                  readBackNormal [] ty value

fn=VPi 1 VUnit (MkTypeClosure [] "k" Unit)
fn2=VPi 1 fn (MkTypeClosure [] "k" Unit)
env=[("s",VNeu fn (NVar "s")),("k",VNeu fn2 (NVar "k"))]

import Data.List
import Data.Vect
import Data.SortedMap
Mult=Nat --For now
scale : Mult -> Mult -> Mult
scale n m = n * m

sum : Mult -> Mult -> Mult
sum n m = n + m

Zero : Mult
Zero = 0

One : Mult
One = 1

AcceptableZero : Mult -> Bool
AcceptableZero m = m==0

AcceptableOne : Mult -> Bool
AcceptableOne m = m==1

nextName : String -> String
nextName x = x ++ "'"

freshen : List String -> String -> String
freshen used x = let x=if not (x=="") then x else "x" in if elem x used then freshen used (nextName x) else x

Used=SortedMap String Mult
EmptyUsed : Used
EmptyUsed = SortedMap.empty 


mutual
  data PreClosure = MkPreClosure String Pretype
  data Pretype = Pi String Mult Pretype Pretype |
    Sigma String Mult Pretype Pretype |
    Unit |
    Bool |
    El Preterm |
    Set

  data Preterm = Var String |
    Abs String Mult Pretype Preterm |
    App Used Preterm Used Preterm Pretype|
    Pair Used Preterm Used Preterm|
    Fst Preterm Pretype|
    Snd Preterm Pretype|
    TBool |
    True |
    False |
    Star | 
    Elim PreClosure Used Preterm Used Preterm Used Preterm |
    TPi String Mult Preterm Preterm
  -- Pair/Unit binding later
  -- dependent function type?

get : String -> List String -> Maybe Nat
get sym (x::xs)=if sym==x then Just ((length xs)) else get sym xs
get _ [] = Nothing

mutual
    TypeαEquivAux : Pretype -> Pretype -> List String -> List String -> Bool

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

    TypeαEquiv : Pretype -> Pretype -> Bool
    TypeαEquiv a b = TypeαEquivAux a b [] []



    αEquivAux : Preterm -> Preterm -> List String -> List String -> Bool

    αEquivAux (Var x) (Var y) map1 map2 = case (get x map1, get y map2) of
                                            (Nothing, Nothing) => x==y
                                            (Just a, Just b) => a==b
                                            _ => False

    αEquivAux (Abs x mult1 ty1 b1) (Abs y mult2 ty2 b2) map1 map2 = let bigger1 = x::map1 in let bigger2 = y::map2 in (αEquivAux b1 b2 bigger1 bigger2) && mult1==mult2 && (TypeαEquivAux ty1 ty2 bigger1 bigger2);
    αEquivAux (App u1 a1 v1 b1 _) (App u2 a2 v2 b2 _) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2 -- u1=u2?

    αEquivAux (Pair u1 a1 v1 b1) (Pair u2 a2 v2 b2) map1 map2 = αEquivAux a1 a2 map1 map2 && αEquivAux b1 b2 map1 map2 -- u1=u2?

    αEquivAux (Fst e1 _) (Fst e2 _) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux (Snd e1 _) (Snd e2 _) map1 map2 = αEquivAux e1 e2 map1 map2
    αEquivAux TBool TBool _ _ = True
    αEquivAux True True _ _ = True
    αEquivAux False False _ _ = True
    αEquivAux Star Star _ _ = True
    αEquivAux (Elim _ _ t1 _ f1 _ b1) (Elim _ _ t2 _ f2 _ b2) map1 map2 = αEquivAux t1 t2 map1 map2 && αEquivAux f1 f2 map1 map2 && αEquivAux b1 b2 map1 map2
    αEquivAux (TPi x m1 a1 b1) (TPi y m2 a2 b2) map1 map2 = αEquivAux a1 a2 map1 map2
      && let bigger1 = x::map1 in let bigger2 = y::map2 in  αEquivAux b1 b2 bigger1 bigger2
      && m1==m2
    αEquivAux _ _ _ _ = False

    αEquiv : Preterm -> Preterm -> Bool
    αEquiv a b = αEquivAux a b [] []

mutual
    Env : Nat -> Type


    data TypeClosure : Type where
        MkTypeClosure : {n:Nat} -> Env n -> String -> TypeValue -> Pretype -> TypeClosure
    data Closure : Type where
        MkClosure : {n:Nat} -> Env n -> String -> Mult -> TypeValue -> Preterm -> Closure

    data TypeValue = VPi Mult TypeValue TypeClosure | VSigma Mult TypeValue TypeClosure | VBool | VUnit | VEl Value | VSet

    data Value = VAbs Closure | VPair Used Value Used Value | VTBool | VFalse | VTrue | VStar | VNeu TypeValue Neu | VTPi Mult Value Closure
    data Neu = NVar String | NApp Used Neu Used Norm TypeValue | NFst Neu TypeValue | NSnd Neu TypeValue | VElim PreClosure Used Norm Used Norm Used Neu
    data Norm = MkNormal TypeValue Value
    


closureName : Closure -> String
closureName (MkClosure _ name _ _ _) = name
closureTy : Closure -> TypeValue
closureTy (MkClosure _ _ _ ty _) = ty
closureMult : Closure -> Mult
closureMult (MkClosure _ _ m _ _) = m
typeClosureName : TypeClosure -> String
typeClosureName (MkTypeClosure _ name _ _) = name


Env n = Vect n (String, Mult, Value, TypeValue)

zeroEnv : Env n -> Env n
zeroEnv [] = []
zeroEnv ((v,m,tm,ty)::env) = ((v,Zero,tm,ty)::(zeroEnv env))

getFresh : {n:Nat} -> Vect n (String, Mult, Value, TypeValue) -> String -> String
getFresh env var= freshen ((toList env) <&> fst) var

usedLookup : String -> Used -> Mult
usedLookup v used = case lookup v used of 
                      Just m => m
                      Nothing => 0

usedIsEmpty : Used -> Bool
usedIsEmpty used = all (\(_,count) => count == Zero) (Data.SortedMap.toList used)

sumUsed : Used -> Used -> Used
sumUsed u1 u2 = mergeWith sum u1 u2

scaleUsed : Mult -> Used -> Used
scaleUsed m used = SortedMap.fromList (map (\(v,count) => (v,scale m count)) (Data.SortedMap.toList used))

checkUsed : Env n -> Used -> Bool
checkUsed [] used = usedIsEmpty used
checkUsed ((v,m,_,_)::env) used = m==usedLookup v used && checkUsed env (delete v used)

checkAccept : Env n -> Bool
checkAccept [] = True
checkAccept ((_,m,_,_)::env) = AcceptableZero m

checkAcceptExcept : Env n -> String -> Bool
checkAcceptExcept [] var = False
checkAcceptExcept ((v,m,_,_)::env) v2 = if v==v2 then AcceptableOne m && checkAccept env else AcceptableZero m && checkAcceptExcept env v2

take : Env n -> Used -> Env n
take [] used = []
take ((v,m,val,ty)::env) used = (v,usedLookup v used,val,ty)::(take env (delete v used))

envToUsed : Env n -> Used
envToUsed [] = SortedMap.empty
envToUsed ((v,m,_,_)::env) = SortedMap.insert v m (envToUsed env)

Ctx=List (String, Mult, TypeValue, Maybe Value)

typeLookup : Ctx -> String -> Maybe TypeValue
typeLookup [] name = Nothing
typeLookup ((x,mult,ty,val)::ctx) y=if x==y then Just ty else typeLookup ctx y
ctxToEnv : Ctx -> (n:Nat  ** Env n)
ctxToEnv [] = (0**[])
ctxToEnv ((x,mult,ty,val)::ctx) = let (len ** env) = (ctxToEnv ctx) in (S len**((x, case val of
                                 Just v => (mult,v,ty)
                                 Nothing => (mult,VNeu ty (NVar x),ty)
                             )::env))


data Existence = Exists | Erased

mutual
    TypeValueαEquivAux : TypeValue -> TypeValue -> List String -> List String -> Maybe Bool
    ValueαEquivAux : Value -> Value -> List String -> List String -> Maybe Bool
    NeutralαEquivAux : Neu -> Neu -> List String -> List String -> Maybe Bool

    TypeValueαEquiv : TypeValue -> TypeValue -> Maybe Bool
    TypeValueαEquiv ty1 ty2 = TypeValueαEquivAux ty1 ty2 [] []
    
    TypeValueαEquivAux (VPi mult1 dom1 cod1) (VPi mult2 dom2 cod2) m1 m2 = let x1 = typeClosureName cod1 in let x2 = typeClosureName cod1 in do 
                                                                          eq_dom <- TypeValueαEquivAux dom1 dom2 m1 m2
                                                                          cod1 <- evalTypeClosure cod1 (VNeu dom1 (NVar x1))
                                                                          cod2 <- evalTypeClosure cod2 (VNeu dom2 (NVar x2))
                                                                          eq_cod <- TypeValueαEquivAux cod1 cod2 (x1::m1) (x2::m2)
                                                                          Just (eq_dom && eq_cod && mult1==mult2)

    TypeValueαEquivAux (VEl (VTPi m dom1 (MkClosure env x _ dom2 cod))) other m1 m2 = TypeValueαEquivAux (VPi m (VEl dom1) (MkTypeClosure env x dom2 (El cod))) other m1 m2
    TypeValueαEquivAux fst  snd@(VEl (VTPi m dom1 (MkClosure env x _ dom2 cod))) m1 m2 = TypeValueαEquivAux snd fst m1 m2

    TypeValueαEquivAux (VSigma mult1 ty_fst1 ty_snd1) (VSigma mult2 ty_fst2 ty_snd2) m1 m2 = let x1 = typeClosureName ty_snd1 in let x2 = typeClosureName ty_snd1 in do 
                                                                          eq_fst <- TypeValueαEquivAux ty_fst1 ty_fst2 m1 m2
                                                                          ty_snd1 <- evalTypeClosure ty_snd1 (VNeu ty_fst1 (NVar x1))
                                                                          ty_snd2 <- evalTypeClosure ty_snd2 (VNeu ty_fst2 (NVar x2))
                                                                          eq_snd <- TypeValueαEquivAux ty_snd1 ty_snd2 (x1::m1) (x2::m2)
                                                                          Just (eq_fst && eq_snd && mult1==mult2)

    TypeValueαEquivAux VBool VBool _ _ = Just True
    TypeValueαEquivAux VBool (VEl VTBool) _ _ = Just True
    TypeValueαEquivAux (VEl VTBool) VBool _ _ = Just True


    TypeValueαEquivAux VUnit VUnit _ _ = Just True

    TypeValueαEquivAux (VEl x) (VEl y) m1 m2 = ValueαEquivAux x y m1 m2

    TypeValueαEquivAux VSet VSet _ _ = Just True

    TypeValueαEquivAux _ _ _ _ = Just False

    ValueαEquivAux (VAbs c1) (VAbs c2) m1 m2 = let x1 = closureName c1 in let x2 = closureName c1 in do 
                                          eq_dom <- TypeValueαEquivAux (closureTy c1) (closureTy c2) m1 m2
                                          b1 <- evalClosure c1 (VNeu (closureTy c1) (NVar x1)) VSet Erased
                                          b2 <- evalClosure c2 (VNeu (closureTy c2) (NVar x2)) VSet Erased
                                          eq_b <- ValueαEquivAux b1 b2 (x1::m1) (x2::m2)
                                          Just (eq_b && (closureMult c1 == closureMult c2) && eq_dom)
    ValueαEquivAux (VPair _ fst1 _ snd1) (VPair _ fst2 _ snd2) m1 m2= do
                                                         eq_fst <- ValueαEquivAux fst1 fst2 m1 m2
                                                         eq_snd <- ValueαEquivAux snd1 snd2 m1 m2
                                                         Just (eq_fst && eq_snd)
    ValueαEquivAux VTBool VTBool _ _ = Just True
    ValueαEquivAux VFalse VFalse _ _ = Just True
    ValueαEquivAux VTrue VTrue _ _ = Just True
    ValueαEquivAux VStar VStar _ _ = Just True
    ValueαEquivAux (VTPi mult1 dom1 cod1) (VTPi mult2 dom2 cod2) m1 m2 = let x1 = closureName cod1 in let x2 = closureName cod1 in do 
                                                                          eq_dom <- ValueαEquivAux dom1 dom2 m1 m2
                                                                          cod1 <- evalClosure cod1 (VNeu (VEl dom1) (NVar x1)) VSet Erased
                                                                          cod2 <- evalClosure cod2 (VNeu (VEl dom2) (NVar x2)) VSet Erased
                                                                          eq_cod <- ValueαEquivAux cod1 cod2 (x1::m1) (x2::m2)
                                                                          Just (eq_dom && eq_cod && mult1==mult2) 

    ValueαEquivAux (VNeu ty1 neu1) (VNeu ty2 neu2) m1 m2 = do 
                                                            eq_ty <- TypeValueαEquivAux ty1 ty2 m1 m2
                                                            eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                            Just (eq_ty && eq_neu)

    ValueαEquivAux _ _ _ _ = Just False


    NeutralαEquivAux (NVar x) (NVar y) m1 m2 = case (get x m1, get y m2) of
                                            (Nothing, Nothing) => Just (x==y)
                                            (Just a, Just b) => Just (a==b)
                                            _ => Just False

    NeutralαEquivAux (NApp _ neu1 _ (MkNormal ty1 val1) _) (NApp _ neu2 _ (MkNormal ty2 val2) _) m1 m2 = do
                                                                                  eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                                                  eq_ty <- TypeValueαEquivAux ty1 ty2 m1 m2
                                                                                  eq_val <- ValueαEquivAux val1 val2 m1 m2
                                                                                  Just (eq_neu && eq_ty && eq_val)
    NeutralαEquivAux (NFst neu1 _) (NFst neu2 _) m1 m2 = NeutralαEquivAux neu1 neu2 m1 m2
    NeutralαEquivAux (NSnd neu1 _) (NSnd neu2 _) m1 m2 = NeutralαEquivAux neu1 neu2 m1 m2
    NeutralαEquivAux (VElim _ _ (MkNormal tty1 tval1) _ (MkNormal fty1 fval1) _ neu1) (VElim _ _ (MkNormal tty2 tval2) _ (MkNormal fty2 fval2) _ neu2) m1 m2 = do
                                                                                  eq_neu <- NeutralαEquivAux neu1 neu2 m1 m2
                                                                                  eq_tty <- TypeValueαEquivAux tty1 tty2 m1 m2
                                                                                  eq_fty <- TypeValueαEquivAux fty1 fty2 m1 m2
                                                                                  eq_tval <- ValueαEquivAux tval1 tval2 m1 m2
                                                                                  eq_fval <- ValueαEquivAux fval1 fval2 m1 m2
                                                                                  Just (eq_neu && eq_tty && eq_fty && eq_tval && eq_fval)
    NeutralαEquivAux _ _ _ _ = Just False



    eval : {n:Nat} -> Env n -> Preterm -> TypeValue -> Existence -> Maybe Value


    eval env (Var x) ty existence = evalVar env x ty existence
    eval env (Abs x mult1 ty1 body) (VPi mult2 dom cod) existence = let x'=getFresh env x in let xVal=VNeu dom (NVar x') in do
                                    ty1 <- typeEval (zeroEnv env) ty1
                                    ty_eq <- TypeValueαEquiv dom ty1
                                    output_ty <- evalTypeClosure cod xVal
                                    _ <- evalClosure (MkClosure env x mult1 ty1 body) xVal output_ty existence
                                    if ty_eq && mult1==mult2 then Just (VAbs (MkClosure env x mult1 ty1 body)) else Nothing

    eval env (Abs x mult1 ty1 body) (VEl (VTPi mult2 dom1 (MkClosure cenv y m (VEl dom2) cod))) existence = eval env (Abs x mult1 ty1 body) (VPi mult2 (VEl dom1) (MkTypeClosure cenv y (VEl dom2) (El cod))) existence

    eval env TBool VSet existence = Just VTBool
    eval env True VBool existence = Just VTrue
    eval env True (VEl VTBool) existence = Just VTrue
    eval env False VBool existence = Just VFalse
    eval env False (VEl VTBool) existence = Just VFalse
    eval env Star VUnit existence = Just VStar

    eval env (App u rator v rand (Pi var mult dom cod)) ty existence = let argExist=if mult==0 then Erased else existence in do
                            dom <- typeEval (zeroEnv env) dom
                            arg <- eval (take env v) rand dom argExist
                            cod_closure <- Just (MkTypeClosure env var dom cod)
                            fun <- eval (take env u) rator (VPi mult dom cod_closure) existence 
                            output_ty <- evalTypeClosure cod_closure arg
                            ty_eq <- TypeValueαEquiv ty output_ty
                            output <- doApply u fun v arg output_ty existence
                            if ty_eq && checkUsed env (sumUsed u (scaleUsed mult v)) then Just output else Nothing

    eval env (Pair u a v b) (VSigma mult fst_ty snd_ty) existence=  do
                            a <- eval (take env u) a fst_ty existence 
                            snd_ty <- evalTypeClosure snd_ty a
                            b <- eval (take env v) b snd_ty existence 
                            if checkUsed env (sumUsed u v) then Just (VPair u a v b) else Nothing

    eval env (Fst pair (Sigma var mult fst_ty snd_ty)) ty Erased=  do
                            fst_ty <- typeEval (zeroEnv env) fst_ty
                            snd_ty <- Just (MkTypeClosure env var fst_ty snd_ty)
                            pair <- eval env pair (VSigma mult fst_ty snd_ty) Erased
                            fst <- doFst pair
                            Just fst

    eval env (Fst pair p_ty) ty Exists = Nothing

    eval env (Snd pair (Sigma var mult fst_ty snd_ty)) ty Erased= do
                            fst_ty <- typeEval (zeroEnv env) fst_ty
                            snd_ty <- Just (MkTypeClosure env var fst_ty snd_ty)
                            pair <- eval env pair (VSigma mult fst_ty snd_ty) Erased
                            snd <- doSnd pair
                            Just snd

    eval env (Snd pair p_ty) ty Exists = Nothing

    eval env (Elim st u t v f w b) ty existence = do
                            b <- eval env b VBool existence
                            tty <- evalPreClosure (zeroEnv env) st VTrue VBool
                            fty <- evalPreClosure (zeroEnv env) st VFalse VBool
                            output_ty  <- evalPreClosure (zeroEnv env) st b VBool
                            ty_eq <- TypeValueαEquiv ty output_ty
                            t <- eval env t tty existence
                            f <- eval env f tty existence
                            if ty_eq then case b of 
                                   VTrue => Just t
                                   VFalse => Just f 
                                   VNeu _ neu => Just (VNeu output_ty (VElim st u (MkNormal tty t) v (MkNormal fty f) w neu))
                                   _ => Nothing
                                   else Nothing
    eval env (TPi x m dom cod) VSet Erased = do
                                 dom <- eval env dom VSet existence
                                 Just (VTPi m dom (MkClosure env x m (VEl dom) cod)) 


    eval _ _ _ _ = Nothing
                            


    evalVar : {n:Nat} -> Env n -> String -> TypeValue -> Existence -> Maybe Value
    evalVar env x ty existence = do
                           i <- findIndex (\y=> x==fst y) env
                           eq_ty <- TypeValueαEquiv ty (snd (snd (snd (index i env))))
                           if eq_ty && case existence of 
                                                                                 Exists => checkAcceptExcept env x 
                                                                                 Erased => checkAccept env
                                                                               then Just (fst (snd (snd (index i env)))) else Nothing
    evalPreClosure : {n:Nat} -> Env n-> PreClosure -> Value -> TypeValue -> Maybe TypeValue
    evalPreClosure env (MkPreClosure x body) val ty = if x=="" then typeEval (zeroEnv env) body else typeEval ((x,0,val,ty)::(zeroEnv env)) body

    evalClosure : Closure -> Value -> TypeValue -> Existence -> Maybe Value
    evalClosure (MkClosure env x mult ty1 body) v ty2 existence = let mult = case existence of 
                                                                                 Exists => mult 
                                                                                 Erased => Zero
                                                                              in if x=="" then eval env body ty2 existence else eval ((x,mult,v,ty1)::env) body ty2 existence

    evalTypeClosure : TypeClosure -> Value -> Maybe TypeValue
    evalTypeClosure (MkTypeClosure env x dom cod) v =if x=="" then typeEval (zeroEnv env) cod else typeEval ((x,0,v,dom)::(zeroEnv env)) cod


    doApply : Used -> Value -> Used ->  Value -> TypeValue -> Existence -> Maybe Value
    doApply _ (VAbs closure) _ arg ty existence = evalClosure closure arg ty existence
    doApply u (VNeu (VPi mult dom cod) neu) v arg ty existence = do
                                              ty2 <- evalTypeClosure cod arg
                                              eq <- TypeValueαEquiv ty ty2
                                              if eq then Just (VNeu ty (NApp u neu v (MkNormal dom arg) (VPi mult dom cod))) else Nothing
    doApply _ _ _ _ _ _ = Nothing

    doFst : Value -> Maybe Value
    doFst (VPair _ v1 _ v2) = Just v1
    doFst (VNeu (VSigma mult fTy sTy) neu) = Just (VNeu fTy (NFst neu (VSigma mult fTy sTy)) )
    doFst _ = Nothing

    doSnd : Value -> Maybe Value
    doSnd (VPair _ v1 _ v2) =Just v2
    doSnd v@(VNeu (VSigma mult fTy sTy) neu) = do
                                             dom <- doFst v
                                             ty <- evalTypeClosure sTy dom
                                             Just (VNeu ty (NSnd neu (VSigma mult fTy sTy)))
    doSnd _ = Nothing

    typeEval : {n:Nat} -> Env n -> Pretype -> Maybe TypeValue
    typeEval env (Pi name mult dom cod) = do
                                            dom <- typeEval env dom
                                            Just (VPi mult dom (MkTypeClosure env name dom cod))
    typeEval env (Sigma name mult fTy sTy) = do
                                            fTy <- typeEval env fTy
                                            Just (VSigma mult fTy (MkTypeClosure env name fTy sTy))

    typeEval env Unit = if checkAccept env then Just (VUnit) else Nothing
    typeEval env Bool = if checkAccept env then Just (VBool) else Nothing
    typeEval env Set = if checkAccept env then Just (VSet) else Nothing
    typeEval env (El expr) = do
                                     expr <- eval env expr VSet Erased
                                     Just (VEl expr)

    readBackTypeNormal : {n:Nat} -> Env n -> TypeValue -> Maybe Pretype
    readBackTypeNormal env (VPi mult dom cod) = let x=getFresh env (typeClosureName cod) in let xVal=VNeu dom (NVar x) in do
                                                pre_dom <- readBackTypeNormal env dom
                                                ty_val_cod <- evalTypeClosure cod xVal
                                                pre_cod <- readBackTypeNormal ((x,0,xVal,dom)::env) ty_val_cod
                                                Just (Pi x mult pre_dom pre_cod)
    readBackTypeNormal env (VSigma mult dom cod) = let x=getFresh env (typeClosureName cod) in let xVal=VNeu dom (NVar x) in do
                                                pre_dom <- readBackTypeNormal env dom
                                                ty_val_cod <- evalTypeClosure cod xVal
                                                pre_cod <- readBackTypeNormal ((x,0,xVal,dom)::env) ty_val_cod
                                                Just (Sigma x mult pre_dom pre_cod)
    readBackTypeNormal env VBool = if checkAccept env then Just Bool else Nothing
    readBackTypeNormal env VUnit =if checkAccept env then Just Unit else Nothing
    readBackTypeNormal env VSet = if checkAccept env then Just Set else Nothing
    readBackTypeNormal env (VEl val) = do
                                      val <- readBackNormal env VSet val Erased
                                      Just (El val)

    readBackNormal : {n:Nat} -> Env n -> TypeValue -> Value -> Existence -> Maybe Preterm
    readBackNeutral : {n:Nat} -> Env n -> Neu -> Existence -> Maybe Preterm

    readBackNormal env (VPi mult dom cod) fun existence = let mult' = case existence of 
                                                                                 Exists => mult 
                                                                                 Erased => Zero
                                                                              in let x = getFresh env(typeClosureName cod) in let xVal = VNeu dom (NVar x) in do
                                                  cod <- evalTypeClosure cod xVal
                                                  body <- doApply (envToUsed env) fun (SortedMap.fromList [("x",1)]) xVal cod existence
                                                  body <- readBackNormal ((x,mult',xVal,dom)::env) cod body existence
                                                  dom <- readBackTypeNormal env dom
                                                  Just (Abs x mult dom body)



    readBackNormal env (VSigma mult fTy sTy) pair Erased= do
                                                  fst <- doFst pair
                                                  snd <- doSnd pair

                                                  sTy <- evalTypeClosure sTy fst

                                                  fst <- readBackNormal env fTy fst Erased
                                                  snd <- readBackNormal env sTy snd Erased
                                                  Just (Pair SortedMap.empty fst SortedMap.empty snd)


    readBackNormal env VUnit _ Erased =if checkAccept env then Just Star else Nothing
    readBackNormal env t (VNeu t′ neu) existence= readBackNeutral env neu existence -- t==t'?

    readBackNormal env (VSigma mult fTy sTy) (VPair u fst v snd) Exists= do

                                              sTy <- evalTypeClosure sTy fst

                                              fst <- readBackNormal env fTy fst Erased
                                              snd <- readBackNormal env sTy snd Erased
                                              Just (Pair u fst v snd)

    readBackNormal env (VSigma mult fTy sTy) _ _ = Nothing
    readBackNormal env VBool VFalse _ =if checkAccept env then Just False else Nothing
    readBackNormal env VBool VTrue _ =if checkAccept env then Just True else Nothing
    readBackNormal env VBool _ _ = Nothing

    readBackNormal env VUnit VStar _ =if checkAccept env then Just Star else Nothing
    readBackNormal env VUnit _ _= Nothing

    readBackNormal env VSet VTBool _ =if checkAccept env then Just TBool else Nothing
    readBackNormal env VSet _  _= Nothing

    readBackNormal env (VEl VTBool) VFalse _= if checkAccept env then Just False else Nothing
    readBackNormal env (VEl VTBool) VTrue _= if checkAccept env then Just False else Nothing


    readBackNormal env (VEl _) _ _= Nothing

    readBackNeutral env (NVar x) _ =Just (Var x)
    readBackNeutral env (NApp u neu v (MkNormal ty arg) ty2) existence = do -- Fix
                                            fun <- readBackNeutral env neu existence
                                            arg <- readBackNormal env ty arg existence
                                            ty2 <- readBackTypeNormal env ty2
                                            Just (App u fun v arg ty2)
    readBackNeutral env (NFst neu ty)  Erased = do
                                         pair <- readBackNeutral env neu Erased
                                         ty <- readBackTypeNormal env ty
                                         Just (Fst pair ty)
    readBackNeutral env (NSnd neu ty) Erased = do
                                         pair <- readBackNeutral env neu Erased
                                         ty <- readBackTypeNormal env ty
                                         Just (Snd pair ty)
    readBackNeutral env (NFst neu ty) Exists=Nothing
    readBackNeutral env (NSnd neu ty) Exists=Nothing

    readBackNeutral env (VElim st u (MkNormal tty t) v (MkNormal fty f) w b) existence=do 
                                                                                       t <- readBackNormal (take env u) tty t existence
                                                                                       f <- readBackNormal (take env v) fty f existence
                                                                                       b <- readBackNeutral (take env w) b existence
                                                                                       Just (Elim st u t v f w b)


    norm : {n:Mult} -> Env n -> Preterm -> Pretype -> Existence -> Maybe Preterm
    norm env expr ty existence = do
                    ty <- typeEval (zeroEnv env) ty
                    value <- eval env expr ty existence
                    readBackNormal env ty value existence


fnType:  String -> Mult -> Pretype -> Pretype -> Pretype
fnType v mult x y= Pi v mult x y

typeVar : String -> Pretype
typeVar v = El (Var v)


-- Examples
example_unit_fn = norm [] (Abs "x" 1 Unit (Var "x")) (fnType "x" 1 Unit Unit) Exists

example_wrong_mult1 = norm [] (Abs "x" 1 Unit (Var "x")) (fnType "x" 2 Unit Unit) Exists
example_wrong_mult2 = norm [] (Abs "x" 2 Unit (Var "x")) (fnType "x" 1 Unit Unit) Exists

example_erased_eta = norm [] (Abs "y" 1 Unit (Var "y")) (fnType "y" 1 Unit Unit) Erased

singleCtx : Ctx
singleCtx=[("T",0,VSet,Nothing)]
example3 = let (n ** env)=ctxToEnv singleCtx in norm env (Abs "x" 1 (typeVar "T") (Var "x")) (fnType "x" 1 (typeVar "T")  (typeVar "T") ) Exists

boolCtx : Ctx
boolCtx=[("b",1,VBool,Nothing)]
example4 = let (n ** env)=ctxToEnv boolCtx in norm env (Elim (MkPreClosure "b" Bool) EmptyUsed True EmptyUsed False (SortedMap.fromList [("b",1)]) (Var "b")) Bool Exists


tm=(Elim (MkPreClosure "b" Bool) EmptyUsed True EmptyUsed False (SortedMap.fromList [("b",1)]) (Var "b"))
pty : Pretype
pty=Bool
env:Env 1
env = [("b", (1, (VNeu VBool (NVar "b"), VBool)))]

ty=typeEval (zeroEnv env) pty
v=do 
ty <- typeEval (zeroEnv env) pty
eval env tm ty Exists

n=do 
ty <- typeEval (zeroEnv env) pty
value <- eval env tm ty Exists
readBackNormal env ty value Exists
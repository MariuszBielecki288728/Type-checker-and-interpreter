-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający rozwiązanie.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko} gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module MariuszBielecki (typecheck, eval) where

-- Importujemy moduły z definicją języka oraz typami potrzebnymi w zadaniu
import AST
import DataTypes
--importujemy moduly pomocnicze
import qualified Data.Map as Map
-------------------------------
--moje typy
--typ pomocniczy do check
data RType p
  = Typed Type
  | RError p String
  deriving (Show, Eq)

--typ pomocniczy do evaluate
data Val
  = VInt Integer
  | VBool Bool
  | VUnit
  | VPair Val Val
  | VList [Val]
  | VError
  deriving (Show, Eq)
-------------------------------



------------------------------------------------------------------------
-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
-------------------------------------------------------------------------

--glowna funkcja---------------------------------------------------------
--najpierw sprawdzam otypowanie ciała programu, jeśli jest poprawne,
--to sprawdzam otypowanie funkcji w ciągu funkcji
typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck fs list expr = case check fs (convertT list) expr of
    Typed TInt      -> checkFun fs fs
    RError x str    -> Error x str
    _               -> Error (getData expr) ("Type error:"
                          ++" Invalid program output type")
-------------------------------------------------------------------------

--funkcja sprawdzająca otypowanie funkcji w ciągu funkcji
checkFun :: [FunctionDef p]->[FunctionDef p] -> TypeCheckResult p
checkFun [] _ = Ok
checkFun (fun:restFuns) fs = let (v, t1, t2) = convertFun fun in
    case check fs (Map.fromList [(v,Typed t1)]) (funcBody fun) of
        Typed x| x==t2 -> checkFun restFuns fs
        RError x str   -> Error x str
        _              -> Error (getData (funcBody fun)) ("Type error: "
                                                ++"bad type of function")

--funkcja pomocnicza check
check  :: [FunctionDef p] -> Map.Map Var (RType p) -> Expr p -> RType p
check fs env expr = case expr of
    EVar  p var   -> case (Map.lookup var env) of
        Just x    -> x
        Nothing   -> RError (getData expr) "Variable not in environment"
    ENum  p _     -> Typed TInt
    EBool p _     -> Typed TBool

    --operatory unarne
    EUnary p op e -> case op of
        UNot      -> case (check fs env e) of
            Typed TBool  -> Typed TBool
            RError x str -> RError x str
            _            -> RError (getData expr) ("Type error: expected bool "
                                                  ++"(\"not\" operator)")
        UNeg      -> case (check fs env e) of
            Typed TInt   -> Typed TInt
            RError x str -> RError x str
            _            -> RError (getData expr) ("Type error: expected int "
                                                  ++"(\"-\" operator)")

    --operatory binarne
    EBinary p op e1 e2 -> case op of

        --operatory boolowskie
        x | elem x [BAnd, BOr]    ->
            case (check fs env e1, check fs env e2) of
                (Typed TBool, Typed TBool) -> Typed TBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError (getData expr) ( "Type error: "
                                                      ++"expected bool and bool"
                                                      ++" (binary operator)")

        --operatory porownania
        x | elem x [BEq, BNeq, BLt, BGt, BLe, BGe] ->
            case (check fs env e1, check fs env e2) of
                (Typed TInt,Typed TInt) -> Typed TBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError (getData expr)  ("Type error: "
                                                      ++"expected int and int "
                                                      ++"(binary operator)")

        --operatory arytmetyczne
        x | elem x [BAdd, BSub, BMul, BDiv, BMod]  ->
            case (check fs env e1, check fs env e2) of
                (Typed TInt,Typed TInt) -> Typed TInt
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError (getData expr) ("Type error: "
                                                     ++"expected int and int "
                                                     ++"(binary operator)")

    --wyrazenie let
    ELet p var e1 e2 -> case (check fs env e1) of
        Typed x      -> check fs (Map.insert var (Typed x) env) e2
        RError x str -> RError x str
    --wyrazenie if
    EIf p e1 e2 e3 -> case (check fs env e1, check fs env e2, check fs env e3) of

        (Typed TBool, Typed x, Typed y) | x == y  -> Typed x
        (Typed x, _, _) | x /= TBool      -> RError (getData expr) ("Type error:"
                                          ++" expected bool in first argument"
                                          ++" (if statement)")

        (RError x str, _, _)    -> RError x str
        (_, RError x str, _)    -> RError x str
        (_, _, RError x str)    -> RError x str
        _                       -> RError (getData expr) ("Type error: "
                                             ++"expected same types in first"
                                             ++" and second argument "
                                             ++"(if statement)")
    --aplikacja funkcji
    EApp  p fsym e -> case (findFunTypes fs fsym, check fs env e) of
        (Just (x, y), Typed t) | x == t -> Typed y
        (Nothing, _)                    -> RError p "Function not in definitions"
        (_,      RError x str)          -> RError x str
        _                               -> RError p ("Type error: "
                                        ++"Unexpected type of argument")


    -- Wyrażenie ()
    EUnit p        -> Typed TUnit

    -- Konstruktor pary
    EPair p e1 e2  -> case (check fs env e1, check fs env e2) of
        (Typed x, Typed y) -> Typed (TPair x y)
        (RError x str, _)  -> RError x str
        (_, RError x str)  -> RError x str



    -- Pierwsza projekcja pary
    EFst  p e      -> case (check fs env e) of
        Typed (TPair x _) -> Typed x
        RError x str      -> RError x str
        _                 -> RError p ("Type error: "
                          ++"Expected type of argument: pair (fst)")

    -- Druga projekcja pary
    ESnd  p e      -> case (check fs env e) of
        Typed (TPair _ y) -> Typed y
        RError x str      -> RError x str
        _                 -> RError p ("Type error: "
                          ++"Expected type of argument: pair (snd)")


    -- Lista pusta (anotowana typem)
    ENil  p (TList typ)    -> Typed  (TList typ)
    ENil  p _              -> RError p "Type error: Wrong type of list"

    -- Konstruktor listy niepustej
    ECons p e1 e2  -> case (check fs env e1, check fs env e2) of
        (Typed x, Typed (TList y))| x == y -> Typed (TList x)
        (RError x str, _)         -> RError x str
        (_, RError x str)         -> RError x str
        (_, Typed (TList _))      -> RError p ("Type error: "
                                  ++"type of each element of list "
                                  ++"has to be the same")
        _                         -> RError p ("Type error: "
                                  ++"second argument of list "
                                  ++"constructor has to be list")


    -- Dopasowanie wzorca dla listy
    EMatchL p e nc (v1, v2, e1) -> case (check fs env e, check fs env nc) of
        (Typed (TList typ), Typed t) -> case
                      (check fs (Map.insert v2 (Typed (TList typ))
                      (Map.insert v1 (Typed typ)
                      env)) e1) of
                            Typed x | x==t -> Typed t
                            RError x str   -> RError x str
                            _              -> RError p ("Type error: "
                                           ++"Types of NilClause "
                                           ++"and ConsClause doesn't match")
        (RError x str, _)                  -> RError x str
        (_, RError x str)                  -> RError x str
        _                                  -> RError p ("Type error: "
                                           ++"Expected list in match")



-----------------------------------------------------------------------
--funkcje pomocnicze do check i checkFun
--funkcja szuka funkcji i zwraca typ jej argumentu i wartosci
findFunTypes :: [FunctionDef p] -> FSym -> Maybe (Type, Type)
findFunTypes list f = find list f where
  find [] _ = Nothing
  find (x:_) f | (funcName x) == f = Just (funcArgType x, funcResType x)
  find (x:xs) f = find xs f

--funkcja konwertuje funkcje na krotke
--(nazwa argumentu, typ argumentu, typ wartości)
convertFun :: FunctionDef p -> (Var, Type, Type)
convertFun f = (funcArg f, funcArgType f, funcResType f)

--funkcja konwertująca srodowisko początkowe do tego uzywanego w check
convertT :: [Var] -> Map.Map Var (RType p)
convertT list = Map.fromList (aux list) where
  aux [] = []
  aux (x:xs) = ((x, Typed TInt):(aux xs))
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że wyrażenie e jest dobrze typowane, tzn.
-- typecheck (map fst input) e = Ok
-----------------------------------------------------------------------
eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval fs list expr = case evaluate fs (convert list) expr of
  VInt int        -> Value int
  _               -> RuntimeError
-----------------------------------------------------

--funkcja pomocnicza evaluate
evaluate ::[FunctionDef p] -> Map.Map Var Val -> Expr p -> Val
evaluate fs list expr = case expr of
  EVar  p var     -> case (Map.lookup var list) of
      Just x      -> x
      Nothing     -> VError
  ENum  p val     -> VInt val
  EBool p val     -> VBool val

  --operatory unarne
  EUnary p op e -> case op of
      UNot        -> case (evaluate fs list e) of
          VBool x -> VBool (not x)
          _       -> VError
      UNeg        -> case (evaluate fs list e) of
          VInt  x -> VInt (-x)
          _       -> VError

  --operatory binarne
  EBinary p op e1 e2 -> case op of

      --operatory boolowskie
      BAnd -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VBool x, VBool y) -> VBool (x && y)
          _                  -> VError
      BOr  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VBool x, VBool y) -> VBool (x || y)
          _                  -> VError
      --operatory porownania
      BEq  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (x == y)
          _                  -> VError
      BNeq  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (not (x == y))
          _                  -> VError
      BLt  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (x < y)
          _                  -> VError
      BGt  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (x > y)
          _                  -> VError
      BLe  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (x <= y)
          _                  -> VError
      BGe  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VBool (x >= y)
          _                  -> VError
      --operatory arytmetyczne
      BAdd  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VInt (x + y)
          _                  -> VError
      BSub  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VInt (x - y)
          _                  -> VError
      BMul  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt x, VInt y)   -> VInt (x * y)
          _                  -> VError
      BDiv  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (div x y)
          _                  -> VError
      BMod  -> case ((evaluate fs list e1), (evaluate fs list e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (mod x y)
          _                  -> VError

  --wyrazenie let
  ELet p var e1 e2 -> case (evaluate fs list e1) of
          VError   -> VError
          x        -> evaluate fs (Map.insert var x list) e2


  --wyrazenie if
  EIf p e1 e2 e3   -> case (evaluate fs list e1) of
      VBool True   -> evaluate fs list e2
      VBool False  -> evaluate fs list e3
      _            -> VError

  --aplikacja funkcji
  EApp p fsym e    -> case evaluate fs list e of
      VError       -> VError
      x            -> let (arg, body) = findFunArgBody fs fsym in
                          evaluate fs (Map.insert arg x list) body

  --wyrazenie ()
  EUnit p          -> VUnit

  -- Konstruktor pary
  EPair p e1 e2    -> case (evaluate fs list e1, evaluate fs list e2) of
      (VError, _)  -> VError
      (_, VError)  -> VError
      (x, y)       -> VPair x y

  -- Pierwsza projekcja pary
  EFst p e         -> case evaluate fs list e of
      VPair x _    -> x
      _            -> VError

  -- Druga projekcja pary
  ESnd p e         -> case evaluate fs list e of
      VPair _ y    -> y
      _            -> VError

  -- konstruktor listy pustej
  ENil p t         -> VList []

  --Konstruktor listy niepustej
  ECons p e1 e2    -> case (evaluate fs list e1,evaluate fs list e2) of
      (VError, _)  -> VError
      (_, VError)  -> VError
      (x, VList y) -> VList (x:y)

  -- Dopasowanie wzorca dla listy
  EMatchL p e nc (h, t, e2) -> case evaluate fs list e of
    VError                  -> VError
    VList []                -> evaluate fs list nc
    VList (x:xs) -> evaluate fs (Map.insert t (VList xs) (Map.insert h x list)) e2
    _                       -> VError



---------------------------------------------------
--funkcje pomocnicze do evaluate
--funkcja konwertuje początkowe srodowisko zmiennych do tego uzywanego w evaluate
convert :: [(Var, Integer)] -> Map.Map Var Val
convert list = (aux list) where
  aux [] = Map.empty
  aux ((x,int):xs) = Map.insert x (VInt int) (aux xs)

-- funkcja szuka funkcji i zwraca (nazwa argumentu, cialo funkcji)
findFunArgBody :: [FunctionDef p] -> FSym -> (Var, Expr p)
findFunArgBody list f = find list f where
  find (x:_) f | (funcName x) == f = (funcArg x, funcBody x)
  find (x:xs) f = find xs f
---------------------------------------------------

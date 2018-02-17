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
data Val p
  = VInt Integer
  | VBool Bool
  | VUnit
  | VPair (Val p) (Val p)
  | VList [Val p]
  | VClos (Map.Map Var (Val p)) Var (Expr p)
  | VGClos [FunctionDef p] (FunctionDef p)
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
typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p
typecheck fs list expr = case checkFun fs fs of
  Ok ->
    case check (convertT fs list) expr of
      Typed TInt      -> Ok
      RError x str    -> Error x str
      _               -> Error (getData expr) ("Type error:"
                            ++" Bad type of whole program")
  er -> er
-------------------------------------------------------------------------

--funkcja sprawdzająca otypowanie funkcji w ciągu funkcji
checkFun :: [FunctionDef p]->[FunctionDef p] -> TypeCheckResult p
checkFun [] _ = Ok
checkFun (fun:restFuns) fs = let (v, t1, t2) = convertFun fun in
    case check (Map.union (convertT fs []) (Map.fromList [(v, t1)])) (funcBody fun) of
        Typed x| x==t2 -> checkFun restFuns fs
        RError x str   -> Error x str
        _              -> Error (getData (funcBody fun)) ("Type error: "
                                                ++"Bad type of function")
--funkcja pomocnicza check
check  ::  Map.Map Var Type -> Expr p -> RType p
check env expr = case expr of
    EVar  p var   -> case (Map.lookup var env) of
        Just x    -> Typed x
        Nothing   -> RError p "Variable not in environment"
    ENum  p _     -> Typed TInt
    EBool p _     -> Typed TBool

    --operatory unarne
    EUnary p op e -> case op of
        UNot      -> case (check env e) of
            Typed TBool  -> Typed TBool
            RError x str -> RError x str
            _            -> RError p ("Type error: expected bool "
                                                  ++"(\"not\" operator)")
        UNeg      -> case (check env e) of
            Typed TInt   -> Typed TInt
            RError x str -> RError x str
            _            -> RError p ("Type error: expected int "
                                                  ++"(\"-\" operator)")

    --operatory binarne
    EBinary p op e1 e2 -> case op of

        --operatory boolowskie
        x | elem x [BAnd, BOr]    ->
            case (check env e1, check env e2) of
                (Typed TBool, Typed TBool) -> Typed TBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p ( "Type error: "
                                                      ++"expected bool and bool"
                                                      ++" (binary operator)")

        --operatory porownania
        x | elem x [BEq, BNeq, BLt, BGt, BLe, BGe] ->
            case (check env e1, check env e2) of
                (Typed TInt,Typed TInt) -> Typed TBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p  ("Type error: "
                                                      ++"expected int and int "
                                                      ++"(binary operator)")

        --operatory arytmetyczne
        x | elem x [BAdd, BSub, BMul, BDiv, BMod]  ->
            case (check env e1, check env e2) of
                (Typed TInt,Typed TInt) -> Typed TInt
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p ("Type error: "
                                                     ++"expected int and int "
                                                     ++"(binary operator)")

    --wyrazenie let
    ELet p var e1 e2 -> case (check env e1) of
        Typed x      -> check (Map.insert var  x env) e2
        RError x str -> RError x str
    --wyrazenie if
    EIf p e1 e2 e3 -> case (check env e1, check env e2, check env e3) of

        (Typed TBool, Typed x, Typed y) | x == y  -> Typed x
        (Typed x, _, _) | x /= TBool      -> RError p ("Type error:"
                                          ++" expected bool in first argument"
                                          ++" (if statement)")

        (RError x str, _, _)    -> RError x str
        (_, RError x str, _)    -> RError x str
        (_, _, RError x str)    -> RError x str
        _                       -> RError p ("Type error: "
                                             ++"expected same types in second"
                                             ++" and third argument "
                                             ++"(if statement)")

    --Lambda-abstrakcja
    EFn p var t1 e -> case check (Map.insert var t1 env) e of
        RError x str -> RError x str
        Typed t2     -> Typed (TArrow t1 t2)

    --Aplikacja funkcji
    EApp  p e1 e2 -> case (check env e1, check env e2) of
        (Typed (TArrow t1 t2), Typed t3)|t1==t3 -> Typed t2
        (Typed (TArrow _ _), Typed _) -> RError p ("Type error: "
                                      ++"wrong type of applicated expression")
        (RError x str, _)    -> RError x str
        (_, RError x str)    -> RError x str
        _                    -> RError p ("Type error: "
                             ++"expression is not function")

    -- Wyrażenie ()
    EUnit p        -> Typed TUnit

    -- Konstruktor pary
    EPair p e1 e2  -> case (check env e1, check env e2) of
        (Typed x, Typed y) -> Typed (TPair x y)
        (RError x str, _)  -> RError x str
        (_, RError x str)  -> RError x str



    -- Pierwsza projekcja pary
    EFst  p e      -> case (check env e) of
        Typed (TPair x _) -> Typed x
        RError x str      -> RError x str
        _                 -> RError p ("Type error: "
                          ++"Expected type of argument: pair (fst)")

    -- Druga projekcja pary
    ESnd  p e      -> case (check env e) of
        Typed (TPair _ y) -> Typed y
        RError x str      -> RError x str
        _                 -> RError p ("Type error: "
                          ++"Expected type of argument: pair (snd)")


    -- Lista pusta (anotowana typem)
    ENil  p (TList typ)    -> Typed  (TList typ)
    ENil  p _              -> RError p "Type error: Wrong type of list"

    -- Konstruktor listy niepustej
    ECons p e1 e2  -> case (check env e1, check env e2) of
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
    EMatchL p e nc (v1, v2, e1) -> case (check env e, check env nc) of
        (Typed (TList typ), Typed t) -> case
                      (check (Map.insert v2 (TList typ)
                      (Map.insert v1  typ
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
--funkcja konwertuje funkcje na krotke
--(nazwa argumentu, typ argumentu, typ wartości)
convertFun :: FunctionDef p -> (Var, Type, Type)
convertFun f = (funcArg f, funcArgType f, funcResType f)

--funkcja konwertująca srodowiska początkowe do tego uzywanego w check
convertT :: [FunctionDef p] -> [Var] -> Map.Map Var Type
convertT fs list = Map.union (aux1 list) (aux2 fs) where

  aux1 [] = Map.empty
  aux1 (x:xs) = Map.insert x TInt (aux1 xs)

  aux2 [] = Map.empty
  aux2 (x:xs) = Map.insert (funcName x)
                           (TArrow (funcArgType x) (funcResType x))
                           (aux2 xs)
-----------------------------------------------------------------------


-----------------------------------------------------------------------
-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że wyrażenie e jest dobrze typowane, tzn.
-- typecheck (map fst input) e = Ok
-----------------------------------------------------------------------
eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult
eval fs envi expr = case evaluate (convert fs envi) expr of
  VInt int        -> Value int
  _               -> RuntimeError
-----------------------------------------------------

--funkcja pomocnicza evaluate
evaluate :: Map.Map Var (Val p) -> Expr p -> Val p
evaluate envi expr = case expr of
  EVar  p var     -> case (Map.lookup var envi) of
      Just x      -> x
      Nothing     -> VError
  ENum  p val     -> VInt val
  EBool p val     -> VBool val

  --operatory unarne
  EUnary p op e -> case op of
      UNot        -> case (evaluate envi e) of
          VBool x -> VBool (not x)
          _       -> VError
      UNeg        -> case (evaluate envi e) of
          VInt  x -> VInt (-x)
          _       -> VError
--pozdro elo
  --operatory binarne
  EBinary p op e1 e2 -> case op of

      --operatory boolowskie
      BAnd -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VBool x, VBool y) -> VBool (x && y)
          _                  -> VError
      BOr  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VBool x, VBool y) -> VBool (x || y)
          _                  -> VError
      --operatory porownania
      BEq  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (x == y)
          _                  -> VError
      BNeq  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (not (x == y))
          _                  -> VError
      BLt  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (x < y)
          _                  -> VError
      BGt  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (x > y)
          _                  -> VError
      BLe  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (x <= y)
          _                  -> VError
      BGe  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VBool (x >= y)
          _                  -> VError
      --operatory arytmetyczne
      BAdd  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VInt (x + y)
          _                  -> VError
      BSub  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VInt (x - y)
          _                  -> VError
      BMul  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt x, VInt y)   -> VInt (x * y)
          _                  -> VError
      BDiv  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (div x y)
          _                  -> VError
      BMod  -> case ((evaluate envi e1), (evaluate envi e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (mod x y)
          _                  -> VError

  --wyrazenie let
  ELet p var e1 e2 -> case (evaluate envi e1) of
          VError   -> VError
          x        -> evaluate (Map.insert var x envi) e2


  --wyrazenie if
  EIf p e1 e2 e3   -> case (evaluate envi e1) of
      VBool True   -> evaluate envi e2
      VBool False  -> evaluate envi e3
      _            -> VError

  --Lambda-abstrakcja
  EFn p var t expr -> VClos envi var expr

  --aplikacja funkcji
  EApp p e1 e2    -> case (evaluate envi e1,evaluate envi e2) of
      (_, VError) -> VError
      (VClos env var expr, val) -> evaluate
                                      (Map.insert var val env)
                                      expr
      (VGClos env f, val) -> evaluate (Map.insert
                                          (funcArg f)
                                          val
                                          (convert env []))
                                      (funcBody f)

  --wyrazenie ()
  EUnit p          -> VUnit

  -- Konstruktor pary
  EPair p e1 e2    -> case (evaluate envi e1, evaluate envi e2) of
      (VError, _)  -> VError
      (_, VError)  -> VError
      (x, y)       -> VPair x y

  -- Pierwsza projekcja pary
  EFst p e         -> case evaluate envi e of
      VPair x _    -> x
      _            -> VError

  -- Druga projekcja pary
  ESnd p e         -> case evaluate envi e of
      VPair _ y    -> y
      _            -> VError

  -- konstruktor listy pustej
  ENil p t         -> VList []

  --Konstruktor listy niepustej
  ECons p e1 e2    -> case (evaluate envi e1,evaluate envi e2) of
      (VError, _)  -> VError
      (_, VError)  -> VError
      (x, VList y) -> VList (x:y)

  -- Dopasowanie wzorca dla listy
  EMatchL p e nc (h, t, e2) -> case evaluate envi e of
    VError                  -> VError
    VList []                -> evaluate envi nc
    VList (x:xs) -> evaluate (Map.insert t (VList xs) (Map.insert h x envi)) e2
    _                       -> VError



---------------------------------------------------
--funkcje pomocnicze do evaluate
--funkcja konwertuje początkowe srodowisko zmiennych do tego uzywanego w evaluate
convert :: [FunctionDef p] -> [(Var, Integer)] -> Map.Map Var (Val p)
convert fs list = Map.union (aux1 list) (aux2 fs fs) where

  aux1 [] = Map.empty
  aux1 ((x,int):xs) = Map.insert x (VInt int) (aux1 xs)

  aux2 [] _ = Map.empty
  aux2 (f:xs) fs = Map.insert (funcName f) (VGClos fs f) (aux2 xs fs)

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
-- Importujemy moduly pomocnicze
import qualified Data.Map as Map
-------------------------------
--moje typy
--typ pomocniczy do check
data RType q
  = RInt
  | RBool
  | RError q String
  deriving (Show, Eq)
-- typ pomocniczy do evaluate
data Val
  = VInt Integer
  | VBool Bool
  | VError
  deriving (Show, Eq)
--------------------------------




-------------------------------------------------------------------------
-- Funkcja sprawdzająca typy
-- Dla wywołania typecheck vars e zakładamy, że zmienne występujące
-- w vars są już zdefiniowane i mają typ int, i oczekujemy by wyrażenia e
-- miało typ int
-------------------------------------------------------------------------

--glowna funkcja---------------------------------------------------------
typecheck :: [Var] -> Expr p -> TypeCheckResult p
typecheck list expr = case check (convertT list) expr of
  RInt            -> Ok
  RError x str    -> Error x str
  _               -> Error (getData expr) "Type error: Invalid output type"
-------------------------------------------------------------------------

--funkcja pomocnicza check
check  :: Map.Map Var (RType p) -> Expr p -> RType p
check list expr = case expr of
    EVar  p var   -> case (Map.lookup var list) of
        Just x    -> x
        Nothing   -> RError p "variable not in environment"
    ENum  p _     -> RInt
    EBool p _     -> RBool

    --operatory unarne
    EUnary p op e -> case op of
        UNot      -> case (check list e) of
            RBool        -> RBool
            RError x str -> RError x str
            _            -> RError p ("Type error: expected bool "
                                                  ++"(\"not\" operator)")
        UNeg      -> case (check list e) of
            RInt         -> RInt
            RError x str -> RError x str
            _            -> RError p ("Type error: expected int "
                                                  ++"(\"-\" operator)")

    --operatory binarne
    EBinary p op e1 e2 -> case op of

        --operatory boolowskie
        x | elem x [BAnd, BOr]                     ->
            case (check list e1, check list e2) of
                (RBool, RBool)    -> RBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p ( "Type error: "
                                                 ++"expected bool and bool "
                                                 ++"(binary operator)")

        --operatory porownania
        x | elem x [BEq, BNeq, BLt, BGt, BLe, BGe] ->
            case (check list e1, check list e2) of
                (RInt,RInt)       -> RBool
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p  ("Type error: "
                                                 ++"expected int and int "
                                                 ++"(binary operator)")

        --operatory arytmetyczne
        x | elem x [BAdd, BSub, BMul, BDiv, BMod]  ->
            case (check list e1, check list e2) of
                (RInt,RInt)       -> RInt
                (RError x str, _) -> RError x str
                (_, RError x str) -> RError x str
                _                 -> RError p ("Type error: "
                                                ++"expected int and int "
                                                ++"(binary operator)")

    --wyrazenie let
    ELet p var e1 e2 -> case check list e1 of
        RBool        -> check (Map.insert var RBool list) e2
        RInt         -> check (Map.insert var RInt list) e2
        RError x str -> RError x str
    --wyrazenie if
    EIf p e1 e2 e3 -> case (check list e1, check list e2, check list e3) of

        (RBool, RInt, RInt)     -> RInt
        (RBool, RBool, RBool)   -> RBool
        (RInt, _, _)            -> RError p ("Type error: "
                                          ++"expected bool in the first argument"
                                          ++" (if statement)")

        (RError x str, _, _)    -> RError x str
        (_, RError x str, _)    -> RError x str
        (_, _, RError x str)    -> RError x str
        _                       -> RError p ("Type error: "
                                             ++"expected same types in the second"
                                             ++" and the third argument "
                                             ++"(if statement)")


-----------------------------------------------------------------------
-- Funkcja obliczająca wyrażenia
-- Dla wywołania eval input e przyjmujemy, że dla każdej pary (x, v)
-- znajdującej się w input, wartość zmiennej x wynosi v.
-- Możemy założyć, że wyrażenie e jest dobrze typowane, tzn.
-- typecheck (map fst input) e = Ok
-----------------------------------------------------------------------

--funkcja glowna-------------------------------------
eval :: [(Var,Integer)] -> Expr p -> EvalResult
eval list expr = case evaluate (convert list) expr of
  VInt int        -> Value int
  _               -> RuntimeError
-----------------------------------------------------

--funkcja pomocnicza evaluate
evaluate :: Map.Map Var Val -> Expr p -> Val
evaluate list expr = case expr of
  EVar  p var     -> case (Map.lookup var list) of
      Just x      -> x
      Nothing     -> VError
  ENum  p val     -> VInt val
  EBool p val     -> VBool val

  --operatory unarne
  EUnary p op e -> case op of
      UNot        -> case (evaluate list e) of
          VBool x -> VBool (not x)
          _       -> VError
      UNeg        -> case (evaluate list e) of
          VInt  x -> VInt (-x)
          _       -> VError

  --operatory binarne
  EBinary p op e1 e2 -> case op of

      --operatory boolowskie
      BAnd -> case ((evaluate list e1), (evaluate list e2)) of
          (VBool x, VBool y) -> VBool (x && y)
          _                  -> VError
      BOr  -> case ((evaluate list e1), (evaluate list e2)) of
          (VBool x, VBool y) -> VBool (x || y)
          _                  -> VError
      --operatory porownania
      BEq  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (x == y)
          _                  -> VError
      BNeq  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (not (x == y))
          _                  -> VError
      BLt  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (x < y)
          _                  -> VError
      BGt  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (x > y)
          _                  -> VError
      BLe  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (x <= y)
          _                  -> VError
      BGe  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VBool (x >= y)
          _                  -> VError
      --operatory arytmetyczne
      BAdd  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VInt (x + y)
          _                  -> VError
      BSub  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VInt (x - y)
          _                  -> VError
      BMul  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt x, VInt y)   -> VInt (x * y)
          _                  -> VError
      BDiv  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (div x y)
          _                  -> VError
      BMod  -> case ((evaluate list e1), (evaluate list e2)) of
          (VInt _, VInt 0)   -> VError
          (VInt x, VInt y)   -> VInt (mod x y)
          _                  -> VError

  --wyrazenie let
  ELet p var e1 e2 -> case (evaluate list e1) of
          VError   -> VError
          x        -> evaluate (Map.insert var x list) e2


  --wyrazenie if
  EIf p e1 e2 e3   -> case (evaluate list e1) of
    VBool True     -> evaluate list e2
    VBool False    -> evaluate list e3
    _              -> VError


---------------------------------------------------
--funkcje pomocnicze do check
convertT :: [Var] -> Map.Map Var (RType p)
convertT list =  aux list where
  aux [] = Map.empty
  aux (x:xs) = Map.insert x RInt (aux xs)

---------------------------------------------------
--funkcje pomocnicze do evaluate
convert :: [(Var, Integer)] -> Map.Map Var Val
convert list = (aux list) where
  aux [] = Map.empty
  aux ((x,int):xs) = Map.insert x (VInt int) (aux xs)


---------------------------------------------------

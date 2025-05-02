{-# LANGUAGE GADTs #-}

--         ∞
-- fix f = ⊔ fⁱ ⊥
--        i=0
fix :: (a -> a) -> a
fix f = f (fix f)

type Iden = String
type Σ = Iden -> Int

update :: Σ -> Iden -> Int -> Σ
update σ v n v' = if v == v' then n else σ v'

eInicial, eIniTest :: Σ
eInicial = \v -> undefined
eIniTest = \v -> 0

{- Ω ≈ (Σ' + Z × Ω + Z → Ω)⊥ -}
data Ω = Normal Σ | Abort Σ | Out (Int, Ω) | In (Int -> Ω)
{- Notar:
   * Normal : Σ → Ω
   * Abort  : Σ → Ω
   * Out    : (Z, Ω) → Ω
   * In     : (Z → Ω) → Ω
-}

data Expr a where
  -- Expresiones enteras
  Const  :: Int       -> Expr Int                      -- n
  Var    :: String    -> Expr Int                      -- v
  Plus   :: Expr Int  -> Expr Int -> Expr Int          -- e + e'
  Dif    :: Expr Int  -> Expr Int -> Expr Int          -- e - e'
  Times  :: Expr Int  -> Expr Int -> Expr Int          -- e * e'
  Div    :: Expr Int  -> Expr Int -> Expr Int          -- e / e'
  -- Expresiones booleanas
  Eq          :: Expr Int  -> Expr Int -> Expr Bool         -- e = e'
  NotEq       :: Expr Int  -> Expr Int -> Expr Bool         -- e /= e'
  LessThan    :: Expr Int -> Expr Int -> Expr Bool          -- e < e'
  LessThanEq  :: Expr Int -> Expr Int -> Expr Bool          -- e <= e'
  -- Comandos
  Skip   :: Expr Ω                                    -- skip
  Local  :: Iden -> Expr Int -> Expr Ω -> Expr Ω      -- newvar v := e in e'
  Assign :: Iden -> Expr Int -> Expr Ω                -- v := e
  Fail   :: Expr Ω                                    -- fail
  Catch  :: Expr Ω -> Expr Ω -> Expr Ω                -- catch c with c'
  While  :: Expr Bool -> Expr Ω -> Expr Ω             -- while b do c
  If     :: Expr Bool -> Expr Ω  -> Expr Ω -> Expr Ω  -- if b then c else c'
  Seq    :: Expr Ω -> Expr Ω -> Expr Ω                -- c ; c'
  Output :: Expr Int -> Expr Ω                        -- !e
  Input  :: Iden -> Expr Ω                            -- ?v
    
class DomSem dom where 
  sem :: Expr dom -> Σ -> dom

instance DomSem Int where
  sem (Const a)    _    = a
  sem (Var v)      σ    = σ v
  sem (Plus e1 e2) σ    = sem e1 σ + sem e2 σ
  sem (Dif e1 e2) σ     = sem e1 σ - sem e2 σ
  sem (Times e1 e2) σ   = sem e1 σ * sem e2 σ
  sem (Div e1 e2) σ     =
    if sem e2 σ == 0
      then undefined
      else sem e1 σ `div` sem e2 σ

instance DomSem Bool where
  sem (Eq e1 e2) σ          = sem e1 σ == sem e2 σ
  sem (NotEq e1 e2) σ       = sem e1 σ /= sem e2 σ
  sem (LessThan e1 e2) σ    = sem e1 σ < sem e2 σ
  sem (LessThanEq e1 e2) σ  = sem e1 σ <= sem e2 σ

(*.) :: (Σ -> Ω) -> Ω -> Ω
(*.) f (Normal σ)  = f σ
(*.) _ (Abort σ)   = Abort σ
(*.) f (Out (n,ω)) = Out (n, f *. ω)
(*.) f (In g)      = In ((f *.) . g)

(†.) :: (Σ -> Σ) -> Ω -> Ω
(†.) f (Normal σ)  = Normal $ f σ
(†.) f (Abort σ)   = Abort $ f σ
(†.) f (Out (n,ω)) = Out (n, f †. ω)
(†.) f (In g)      = In ((f †.) . g)

(+.) :: (Σ -> Ω) -> Ω -> Ω
(+.) _ (Normal σ)  = Normal σ
(+.) f (Abort σ)   = f σ
(+.) f (Out (n,ω)) = Out (n, f +. ω)
(+.) f (In g)      = In ((f +.) . g)

instance DomSem Ω where
  sem Skip σ            = Normal σ
  sem (Local v n c) σ   =
    let originalValue = σ v -- Se almacena el valor original de v
        updatedState = update σ v (sem n σ) -- Se evalua v en el nuevo valor
        result = sem c updatedState -- Se evalua c en el nuevo estado
    in (†.) (\state -> update state v originalValue) result
  sem (Assign v n) σ    = Normal (update σ v (sem n σ))
  sem Fail σ            = Abort σ
  sem (Catch c1 c2) σ   = (+.) (\state -> sem c2 state) (sem c1 σ)
  sem (While b c) σ     = 
    let fixed_point = fix (\f state ->
                        if sem b state
                          then (*.) f (sem c state) 
                          else Normal state)
    in fixed_point σ
  sem (If b c1 c2) σ    =
    if sem b σ
      then sem c1 σ
      else sem c2 σ
  sem (Seq c1 c2) σ = (*.) (\state -> sem c2 state) (sem c1 σ)
  sem (Output e) σ = Out (sem e σ, Normal σ)
  sem (Input f) σ = In (Normal . update σ f)

{- ################# Funciones de evaluación de dom ################# -}

class Eval dom where 
  eval :: Expr dom -> Σ -> IO ()

instance Eval Int where
  eval e = print . sem e

instance Eval Bool where
  eval e = print . sem e

instance Eval Ω where
  eval e = unrollOmega . sem e
    where unrollOmega :: Ω -> IO ()
          unrollOmega (Normal σ)   = return ()
          unrollOmega (Abort σ)    = putStrLn "Abort"
          unrollOmega (Out (n, ω)) = print n >> unrollOmega ω
          unrollOmega (In f)       = getLine >>= unrollOmega . f . read

-- Ejemplo de Output
progOutput = Seq (Assign "x" (Const 5)) (Output (Var "x"))
ejemploOutput = eval progOutput eInicial

-- Ejemplo de Input
progInput = Input "x"
ejemploInput = eval progInput eInicial

-- Ejemplo combinado de Input y Output
progCombined = Seq 
                (Input "x" ) 
                (Output (Var "x"))
ejemploCombined = eval progCombined eInicial

-- Ejemplo combinado de Input y Output con suma de dos entradas
progCombinedSum = Seq 
                    (Seq (Input "x") (Input "y")) 
                    (Output (Plus (Var "x") (Var "y")))
ejemploCombinedSum = eval progCombinedSum eInicial

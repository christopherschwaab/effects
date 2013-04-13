module Eval where
import Control.Applicative
import Control.Monad.State.Lazy (State, runState, get, put, modify)
import Data.Foldable (foldrM)
import Data.List (find)
import qualified Data.Map as M

data Op = Decide | Lookup | Update deriving (Eq, Show)

data Type = TInt | TBool | TUnit | TEmpty | TList Type
          | (:*) Type Type | (:+) Type Type
          | (:->) Type Type | EffectSig | (:=>) Type Type
          deriving Show
type EffectSig = [(Op, Type, Type)]
type Var = String
infixr 3 `Cons`
data Expr = Var Var
          | Num Int
          | C Computation
          | Tru | Fls
          | Nil | Cons Expr Expr
          | TT
          | Pair Expr Expr
          | InjL Expr | InjR Expr
          | Abs Var Computation
          | (:#) Expr Op
          | Handler [(Expr, Op, Var, Var, Computation)]
                    Var Computation
                    Var Computation
          | Del String [Expr]
          deriving Show
data Computation = Val Expr
                 | Let Var Computation Computation
                 | LetRec Var Var Computation Computation
                 | If Expr Computation Computation
                 | MatchEmpty Expr
                 | MatchPair Expr Var Var Computation
                 | MatchSum Expr Var Computation Var Computation
                 | (:$) Expr Expr
                 | New EffectSig
                 | HandleWith Expr Computation
                 deriving Show

type ResourceMap = M.Map Int V
type EvalS = State (Int, ResourceMap)

type EffectI = (Int, (Op, V, V) -> EvalS (V, V))
data V = Z (Maybe Int)
       | B (Maybe Bool)
       | U (Maybe ())
       | I (Maybe EffectI)
       | L [V]
       | Prod V V
       | Inj1 V
       | Inj2 V
       | FunV (V -> EvalS R)
       | FunR (R -> EvalS R)
data Rt = Value V | Oper EffectI Op V (V -> EvalS R)
type R = Maybe Rt

instance Show V where
  show (Z n) = "(Z " ++ show n ++ ")"
  show (B b) = "(B " ++ show b ++ ")"
  show (U u) = "(U " ++ show u ++ ")"
  show (I (Just (i, r))) = "(I (Just (" ++ show i ++ ", r)))"
  show (I Nothing) = "(I Nothing)"
  show (L vs) = "(L " ++ show vs ++ ")"
  show (Prod v1 v2) = "(Prod " ++ show v1 ++ " " ++ show v2 ++ ")"
  show (Inj1 v) = "(Inj1 " ++ show v ++ ")"
  show (Inj2 v) = "(Inj2 " ++ show v ++ ")"
  show (FunV f) = "FunV"
  show (FunR f) = "FunR"
instance Show Rt where
  show (Value v) = "(Value " ++ show v ++ ")"
  show (Oper (n, r) op v f) =
    "(Oper (" ++ show n ++ ", r) " ++ show op ++ " " ++ show v ++ " FunV" ++ ")"

liftV :: (V -> EvalS R) -> R -> EvalS R
liftV f (Just (Value v)) = f v
liftV f (Just (Oper n op v k)) =
  pure $ Just (Oper n op v (\w -> liftV f =<< k w))
liftV f Nothing = pure Nothing

type Env = Var -> V
extend :: Env -> Var -> V -> Env
extend env x v = \y -> if x == y then v else env y

evalv :: Expr -> Env -> EvalS V
evalv (C c) env = evalc c env >>= \v ->
  case v of
    Just (Value v) -> pure v
    _ -> pure $ L []
evalv (Del f es) env =
  case lookup f dels of
    Just f' -> f' <$> mapM (flip evalv env) es
    _ -> pure $ U Nothing
  where dels = [("-", \[Z (Just v1), Z (Just v2)] -> Z (Just (v1 - v2)))
               ,("@", \[L xs1, L xs2] -> L (xs1 ++ xs2))]
evalv (Var x) env = pure $ env x
evalv (Num n) env = pure $ Z (Just n)
evalv Fls env = pure $ B (Just False)
evalv Tru env = pure $ B (Just True)
evalv TT env = pure $ U (Just ())
evalv Nil env = pure $ L []
evalv (x `Cons` xs) env = do
  v  <- evalv x env
  vs <- evalv xs env
  case vs of
    L vs' -> pure $ L (v:vs')
    _ -> pure $ L []
evalv (Pair e1 e2) env = Prod <$> evalv e1 env <*> evalv e2 env
evalv (InjL e) env = Inj1 <$> evalv e env
evalv (InjR e) env = Inj2 <$> evalv e env
evalv (Abs x c) env =
  pure $ FunV (\v -> evalc c (extend env x v))
evalv (e :# op) env = do
  ev <- evalv e env
  case ev of
    I (Just n) ->
      pure $ FunV (\v -> pure $ Just (Oper n op v (pure . Just . Value)))
    _ -> pure $ FunV (\_ -> pure Nothing)
evalv (Handler hs xv cv xf cf) env = do
  hs' <- foldrM (\(e, op, x, k, c) hs' ->
           case hs' of
             Just hs' -> evalv e env >>= \v ->
               case v of
                 I (Just n) -> pure . Just $ (n, op, x, k, c) : hs'
                 _ -> pure Nothing
             Nothing -> pure Nothing) (Just []) hs
  case hs' of
    Just hs' -> pure $ FunR (\v -> liftV f =<< h hs' v)
    Nothing -> pure $ FunR (liftV f . \_ -> Nothing)
  where f v = evalc cf (extend env xf v)

        h :: [(EffectI, Op, Var, Var, Computation)] -> R -> EvalS R
        h hs' (Just (Value v)) = evalc cv (extend env xv v)
        h hs' (Just (Oper (n, r) op v kappa)) =
          case find (\((ni, ri), opi, x, k, c) -> n == ni && op == opi) hs' of
             Just ((ni, ri), opi, x, k, c) -> do
                 (nextFresh, ss) <- get
                 case M.lookup ni ss of
                   Just s -> do (v', s') <- r (opi, v, s)
                                put (nextFresh, M.insert ni s' ss)
                                evalc c (extend (extend env x v') k (FunV (\u -> h hs' =<< kappa u)))
                   _ -> evalc c (extend (extend env x v) k (FunV (\u -> h hs' =<< kappa u)))
             Nothing -> pure . Just $ Oper (n, r) op v (\v -> h hs' =<< kappa v)

evalc :: Computation -> Env -> EvalS R
evalc (Val v) env = Just . Value <$> evalv v env
evalc (Let x c1 c2) env =
  liftV (\v -> evalc c2 (extend env x v)) =<< evalc c1 env
evalc (LetRec f x c1 c2) env = evalc c2 (extend env f (FunV t))
  where t = \v -> evalc c1 (extend (extend env f (FunV t)) x v)
evalc (If e c1 c2) env = evalv e env >>= \ev ->
  case ev of
    B (Just True)  -> evalc c1 env
    B (Just False) -> evalc c2 env
    _ -> pure Nothing
evalc (MatchEmpty e) env = pure Nothing
evalc (MatchPair e x y c) env = evalv e env >>= \ev ->
  case ev of
    Prod v0 v1 -> evalc c (extend (extend env x v0) y v1)
    _ -> pure Nothing
evalc (MatchSum e x c1 y c2) env = evalv e env >>= \ev ->
  case ev of
    Inj1 v -> evalc c1 (extend env x v)
    Inj2 v -> evalc c2 (extend env y v)
    _ -> pure Nothing
evalc (e1 :$ e2) env = do
  v1 <- evalv e1 env
  v2 <- evalv e2 env
  case v1 of
    FunV f -> f v2
    _ -> pure Nothing
evalc (New eff) env = fresh >>= \n ->
  return . Just . Value . I $ Just (n, undefined)
  where fresh = do (n, ss) <- get
                   put (n+1, ss)
                   return n
evalc (HandleWith e c) env = do
  v <- evalv e env
  case v of
    FunR f -> f =<< evalc c env
    _ -> pure Nothing

eval c = fst $ runState (evalc c undefined) (0, M.empty)

chooser c = Handler [(c, Decide, "x", "k", Var "k" :$ Tru)]
                    "x" (Val (Var "x"))
                    "x" (Val (Var "x"))
simpleChoice = Let "c" (New [(Decide, TUnit, TBool)]) $
               HandleWith (chooser (Var "c")) $
                 Var "c" :# Decide :$ TT

chooseAll c = Handler [(c, Decide, "x", "k",
                        Let "v1" (Var "k" :$ Tru) $
                        Let "v2" (Var "k" :$ Fls) $
                        Val $ Del "@" [Var "v1", Var "v2"])]
                      "x" (Val (Var "x" `Cons` Nil))
                      "x" (Val (Var "x"))
testValue =
  Let "c" (New [(Decide, TUnit, TBool)]) $
  HandleWith (chooseAll (Var "c")) $
    Val $ Num 10

testChooseAll =
  Let "c" (New [(Decide, TUnit, TBool)]) $
  HandleWith (chooseAll (Var "c")) $
    Let "x" (Let "v" (Var "c" :# Decide :$ TT) $
             If (Var "v") (Val (Num 10)) (Val (Num 20))) $
    Val $ Var "x"

testNest =
  Let "c1" (New [(Decide, TUnit, TBool)]) $
  Let "c2" (New [(Decide, TUnit, TBool)]) $
  HandleWith (chooseAll (Var "c1")) $
  HandleWith (chooseAll (Var "c2")) $
    Let "x" (Let "v1" (Var "c1" :# Decide :$ TT) $
             If (Var "v1") (Val (Num 10)) (Val (Num 20))) $
    Let "y" (Let "v2" (Var "c2" :# Decide :$ TT) $
             If (Var "v2") (Val (Num 0)) (Val (Num 5))) $
    Val $ Del "-" [Var "x", Var "y"]

testNest2 =
  Let "c1" (New [(Decide, TUnit, TBool)]) $
  Let "c2" (New [(Decide, TUnit, TBool)]) $
  HandleWith (chooseAll (Var "c2")) $
  HandleWith (chooseAll (Var "c1")) $
    Let "v1" (Var "c1" :# Decide :$ TT) $
    Let "x" (If (Var "v1") (Val (Num 10)) (Val (Num 20))) $
    Let "v2" (Var "c2" :# Decide :$ TT) $
    Let "y" (If (Var "v2") (Val (Num 0)) (Val (Num 5))) $
    Val $ Del "-" [Var "x", Var "y"] `Cons` Nil

testIntState =
  Let "stateHandler"
    (Val $ Abs "r" $ Val $ Abs "x" $
       Val $ Handler [(Var "r", Lookup, "()", "k"
                ,Val $ Abs "s" $ Let "g" (Var "k" :$ Var "s") $
                                 Var "g" :$ Var "s")
               ,(Var "r", Update, "s'", "k"
                ,Val $ Abs "s" $ Let "g" (Var "k" :$ TT) $
                                 Var "g" :$ Var "s'")]
               "y" (Val $ Abs "s" $ Val $ Var "y")
               "f" (Var "f" :$ Var "x")) $
  Let "s" (New [(Lookup, TUnit, TInt)
               ,(Update, TInt, TUnit)]) $
  Let "stateHandler'" (Var "stateHandler" :$ Var "s") $
  Let "stateHandler''" (Var "stateHandler'" :$ Num 0) $
  HandleWith (Var "stateHandler''") $
    Let "_" (Var "s" :# Update :$ (Num 10)) $
    Var "s" :# Lookup :$ TT

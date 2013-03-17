-- An implementation of eff described in:
--  Programming with Algebraic Effects and Handlers
{-# OPTIONS --no-positivity-check --no-termination-check #-}
module eff where
import Level
open import Function using (_∘_; _$_; flip)
open import Data.Bool hiding (if_then_else_)
open import Data.Empty
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc) renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Properties using (strictTotalOrder)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.Core using (Decidable; _≡_; refl)
open import Relation.Nullary
open import Relation.Unary using () renaming (Decidable to  UDecidable)

Var = ℕ
_≟v_ : Decidable {A = Var} _≡_
x ≟v y = x ≟ℕ y

data Const : Set where
data Op : Set where
  Choice : Op
_≟op_ : Decidable {A = Op} _≡_
Choice ≟op Choice = yes refl

mutual
  OpSig = List (Op × Type × Type)

  data EffectType : Set where
    effect_end : OpSig → EffectType

  data Type : Set where
    int : Type
    bool : Type
    unit : Type
    empty : Type
    _⊗_ : Type → Type → Type
    _⊕_ : Type → Type → Type
    _⟶_ : Type → Type → Type
    _⇒_ : Type → Type
    eff : EffectType → Type

operation_∶_⟶_ : Op → Type → Type → Op × Type × Type
operation op ∶ A ⟶ B = op , A , B

mutual
  data OperationMap : Set where
    operation_var_at_↦_ : Op → Var → Var → Computation → OperationMap

  data OperationHandler : Set where
    _#_var_var_↦_ : Expr → Op → Var → Var → Computation → OperationHandler

  data Expr : Set where
    var : Var → Expr
    nat : ℕ → Expr
    bool : Bool → Expr
    const : Const → Expr
    tt : Expr
    _,_ : Expr → Expr → Expr
    left : Expr → Expr
    right : Expr → Expr
    fun_∶_↦_ : Var → Type → Computation → Expr
    _#_ : Expr → Op → Expr
    handler_val_↦_finally_↦_ : List OperationHandler → Var → Computation → Var
                             → Computation → Expr
  
  data Computation : Set where
    val : Expr → Computation
    letc_≡_inn_ : Var → Computation → Computation → Computation
    letrec_[_]≡_inn_ : Var → Var → Computation → Computation  → Computation
    if_then_else_ : Expr → Computation → Computation → Computation
    match_with⊥ : Expr → Computation
    match_withc_,_↦_ : Expr → Var → Var → Computation → Computation
    match_left_↦_right_↦_ : Expr → Var → Computation → Var → Computation
                          → Computation
    _*_ : Expr → Expr → Computation
    new_ : EffectType → Computation
    new_at_withc_end : EffectType → Expr → List OperationMap → Computation
    withe_handle_end : Expr → Computation → Computation

opMapped : OperationMap → Op
opMapped (operation op var _ at _ ↦ _) = op

opComputation : OperationMap → Computation
opComputation (operation _ var _ at _ ↦ c) = c

Context = List (Var × Type)

open import Data.List.Any using (module Membership-≡; here; there; any)
open Membership-≡

_∶_∈_ : Var → Type → Context → Set
x ∶ A ∈ Γ = x , A ∈ Γ

_∋_∶_⟶_ : EffectType → Op → Type → Type → Set
(effect sig end) ∋ op ∶ A ⟶ B = (op , A , B) ∈ sig

infix 2 _⊢e_∶_
data _⊢e_∶_ : Context → Expr → Type → Set where
  ok-var : ∀{x A Γ} → x ∶ A ∈ Γ → Γ ⊢e var x ∶ A
  ok-bool : ∀{Γ b} → Γ ⊢e bool b ∶ bool
  ok-nat : ∀{Γ n} → Γ ⊢e nat n ∶ int
  ok-unit : ∀{Γ} → Γ ⊢e tt ∶ unit
  ok-prod : ∀{Γ e₁ A e₂ B} → Γ ⊢e e₁ ∶ A → Γ ⊢e e₂ ∶ B → Γ ⊢e (e₁ , e₂) ∶ A ⊗ B
  ok-left : ∀{Γ e A B} → Γ ⊢e e ∶ A → Γ ⊢e left e ∶ A ⊕ B
  ok-right : ∀{Γ e A B} → Γ ⊢e e ∶ A → Γ ⊢e right e ∶ A ⊕ B
  ok-op : ∀{Γ op A B e E}
        → Γ ⊢e e ∶ eff E
        → E ∋ op ∶ A ⟶ B
        → Γ ⊢e e # op ∶ A ⟶ B

infix 2 _⊢c_∶_
data _⊢c_∶_ : Context → Computation → Type → Set where
  ok-val : ∀{Γ e A} → Γ ⊢e e ∶ A → Γ ⊢c val e ∶ A
  ok-let : ∀{Γ c₁ A c₂ B x} → Γ ⊢c c₁ ∶ A → (x , A) ∷ Γ ⊢c c₂ ∶ B
         → Γ ⊢c letc x ≡ c₁ inn c₂ ∶ B
  ok-letrec : ∀{Γ f A B x c₁ c₂ C}
            → (x , A) ∷ (f , A ⟶ B) ∷ Γ ⊢c c₁ ∶ B
            → (f , A ⟶ B) ∷ Γ ⊢c c₂ ∶ C
            → Γ ⊢c letrec f [ x ]≡ c₁ inn c₂ ∶ C
  ok-if : ∀{Γ e c₁ c₂ A} → Γ ⊢e e ∶ bool → Γ ⊢c c₁ ∶ A → Γ ⊢c c₂ ∶ A
        → Γ ⊢c if e then c₁ else c₂ ∶ A
  ok-match⊥ : ∀{Γ e A} → Γ ⊢e e ∶ empty → Γ ⊢c match e with⊥ ∶ A
  ok-match× : ∀{Γ e A B x y c C}
            → Γ ⊢e e ∶ A ⊗ B → (y , B) ∷ (x , A) ∷ Γ ⊢c c ∶ C
            → Γ ⊢c match e withc x , y ↦ c ∶ C
  ok-match+ : ∀{Γ e A B x y c₁ c₂ C}
            → Γ ⊢e e ∶ A ⊕ B
            → (x , A) ∷ Γ ⊢c c₁ ∶ C
            → (y , B) ∷ Γ ⊢c c₂ ∶ C
            → Γ ⊢c match e left x ↦ c₁ right y ↦ c₂ ∶ C
  ok-app : ∀{Γ e₁ e₂ A B} → Γ ⊢e e₁ ∶ A ⟶ B → Γ ⊢e e₂ ∶ A
         → Γ ⊢c e₁ * e₂ ∶ B
  ok-new : ∀{Γ E} → Γ ⊢c new E ∶ eff E

open import Relation.Binary using (StrictTotalOrder)
import Data.AVL
open module Map (V : Set) =
    Data.AVL {ℓ = Level.zero} (λ (_ : ℕ) → V)
             (StrictTotalOrder.isStrictTotalOrder strictTotalOrder)

import Category.Monad
open import Category.Monad.State using (State; StateMonad)

EffectIndex = ℕ
mutual
  EffectI = EffectIndex × (Op × V → State (Tree V × ℕ) V)
  data R : Set where
    ιv : V → R
    ιoper : EffectI × Op × V × (V → State (Tree V × ℕ) R) → R
    nothing : R
  data V : Set where
    ιc : Const → V
    ιeff : EffectI → V
    ιn : ℕ → V
    ιb : Bool → V
    ι⋆ : ⊤ → V
    ι× : V × V → V
    ι+ : V ⊎ V → V
    ι→ : (V → State (Tree V × ℕ) R) → V
    ι⇒ : (R → State (Tree V × ℕ) R) → V
    ιv : V ⊎ ℕ × Op × V × (V → R) → V
    nothing : V

open Category.Monad.RawMonad (StateMonad (Tree V × ℕ))

Res = Maybe (V ⊎ EffectI × Op × V × (V → State (Tree V × ℕ) R))
ιres : Res → R
ιres (just (inj₁ v)) = ιv v
ιres (just (inj₂ oper)) = ιoper oper
ιres nothing = nothing

ρres : R → Res
ρres (ιv v) = just (inj₁ v)
ρres (ιoper op) = just (inj₂ op)
ρres nothing = nothing

ρval : Res → V
ρval (just (inj₁ v)) = v
ρval _               = nothing

ρeff : V → Maybe EffectI
ρeff (ιeff e) = just e
ρeff _        = nothing

_† : (V → State (Tree V × ℕ) R) → Res → State (Tree V × ℕ) R
(f †) (just (inj₁ v)) = f v
(f †) (just (inj₂ (n , op , v , k))) =
  return (ιoper (n , op , v , λ v' → f † ∘ ρres =<< k v'))
(f †) nothing = return nothing

Env = Var → V
_[_↦_] : Env → Var → V → Env
(η [ x ↦ v ]) y with x ≟v y
... | yes x≡y = v
... | no  x≢y = η y

mutual
  ⟦_⟧c_ : Computation → Env → State (Tree V × ℕ) R
  ⟦ val e ⟧c η = return ∘ ιv =<< ⟦ e ⟧ η
  ⟦ letc x ≡ c₁ inn c₂ ⟧c η =
    (λ v → ⟦ c₂ ⟧c (η [ x ↦ v ])) † ∘ ρres =<< ⟦ c₁ ⟧c η
  ⟦ letrec f [ x ]≡ c₁ inn c₂ ⟧c η = ⟦ c₂ ⟧c (η [ f ↦ ι→ t ])
    where t = λ v → ⟦ c₁ ⟧c (η [ f ↦ ι→ t ] [ x ↦ v ])
  ⟦ if e then c₁ else c₂ ⟧c η = elim-bool =<< ⟦ e ⟧ η
    where elim-bool : V → State (Tree V × ℕ) R
          elim-bool (ιb true)  = ⟦ c₁ ⟧c η
          elim-bool (ιb false) = ⟦ c₂ ⟧c η
          elim-bool _ = return nothing
  ⟦ match e with⊥ ⟧c η = return nothing
  ⟦ match e left x ↦ c₁ right y ↦ c₂ ⟧c η = elim+ =<< ⟦ e ⟧ η
    where elim+ : V → State (Tree V × ℕ) R
          elim+ (ι+ (inj₁ l)) = ⟦ c₁ ⟧c (η [ x ↦ l ])
          elim+ (ι+ (inj₂ r)) = ⟦ c₂ ⟧c (η [ y ↦ r ])
          elim+ _ = return nothing
  ⟦ match e withc x , y ↦ c ⟧c η = elim× =<< ⟦ e ⟧ η
    where elim× : V → State (Tree V × ℕ) R
          elim× (ι× (v₀ , v₁)) = ⟦ c ⟧c (η [ x ↦ v₀ ] [ y ↦ v₁ ])
          elim× _ = return nothing
  ⟦ e₁ * e₂ ⟧c η = elim→ =<< ⟦ e₁ ⟧ η
    where elim→ : V → State (Tree V × ℕ) R
          elim→ (ι→ f) = f =<< ⟦ e₂ ⟧ η
          elim→ _ = return nothing
  ⟦ new E ⟧c η = fresh-n
    where fresh-n : Tree V × ℕ → R × Tree V × ℕ
          fresh-n (σ , n) = let s = σ , suc n
                            in ιv (ιeff (n , λ _ _ → nothing , s)) , s
  ⟦ withe e handle c end ⟧c η = elim⇒ =<< ⟦ e ⟧ η
    where elim⇒ : V → State (Tree V × ℕ) R
          elim⇒ (ι⇒ f) = f =<< ⟦ c ⟧c η
          elim⇒ _ = return nothing
  ⟦ new E at e withc ops end ⟧c η = new-eff =<< ⟦ e ⟧ η
    where handles? : (op : Op) → UDecidable (_≡_ op ∘ opMapped)
          handles? op (operation op' var _ at _ ↦ _) = op ≟op op'
          r : List OperationMap → Op × V → Tree V × ℕ → V × Tree V × ℕ
          r ops (op , v) (σ , n) with lookup V n σ | any (handles? op) ops
          ... | just s | yes opi = go (proj₁ (find opi)) (σ , n)
            where go : OperationMap → State (Tree V × ℕ) V
                  go (operation _ var x at y ↦ c₁) =
                    return ∘ ρval ∘ ρres =<< ⟦ c₁ ⟧c (η [ x ↦ v ] [ y ↦ s ])
          ... | _ | _ = nothing , σ , n
          new-eff : V → Tree V × ℕ → R × Tree V × ℕ
          new-eff v (σ , n) = let σ' = insert V n v σ
                              in ιv (ιeff (n , r ops)) , σ' , n
  
  ⟦_⟧_ : Expr → Env → State (Tree V × ℕ) V
  ⟦ var x ⟧ η = return (η x)
  ⟦ const c ⟧ η = return (ιc c)
  ⟦ nat n ⟧ η = return (ιn n)
  ⟦ bool b ⟧ η = return (ιb b)
  ⟦ tt ⟧ η = return (ι⋆ tt)
  ⟦ e₁ , e₂ ⟧ η = ⟦ e₁ ⟧ η >>= λ v₁ →
                  ⟦ e₂ ⟧ η >>= λ v₂ →
    return (ι× (v₁ , v₂))
  ⟦ left e ⟧ η = return ∘ ι+ ∘ inj₁ =<< ⟦ e ⟧ η
  ⟦ right e ⟧ η = return ∘ ι+ ∘ inj₂ =<< ⟦ e ⟧ η
  ⟦ fun x ∶ A ↦ c ⟧ η = return $ ι→ (λ v → ⟦ c ⟧c (η [ x ↦ v ]))
  ⟦ e # op ⟧ η = inj-oper =<< ⟦ e ⟧ η
    where inj-oper : V → State (Tree V × ℕ) V
          inj-oper (ιeff i) =
            return $ ι→ (λ v → return $ ιoper (i , op , v , return ∘ ιv))
          inj-oper _ = return nothing
  ⟦ handler hs val xv ↦ cv finally x ↦ cf ⟧ η =
    return $ ι⇒ (λ r → (λ v → ⟦ cf ⟧c (η [ x ↦ v ])) † ∘ ρres
                                =<< h (ρres r) =<< toEffects hs)
    where maybeCons : {A B : Set} → Maybe A × B → Maybe (List (A × B))
                    → Maybe (List (A × B))
          maybeCons (just x , y) (just xs) = just ((x , y) ∷ xs)
          maybeCons _ _ = nothing
          toEffects : List OperationHandler
                    → State (Tree V × ℕ)
                        (Maybe (List (EffectI × Op × Var × Var × Computation)))
          toEffects (e # op var x var k ↦ c ∷ hs) =
            ⟦ e ⟧ η >>= λ v → toEffects hs >>= λ vs →
            return (maybeCons (ρeff v , op , x , k , c) vs)
          toEffects [] = return (just [])

          proj-effect-index : EffectI × Op × Var × Var × Computation
                            → EffectIndex
          proj-effect-index ((n , _) , _ , _ , _) = n
          proj-op : EffectI × Op × Var × Var × Computation → Op
          proj-op ((_ , _) , op , _ , _) = op
          ≟× : (n : EffectIndex) → (op : Op)
             → UDecidable (λ e → n ≡ proj-effect-index e × op ≡ proj-op e)
          ≟× n op ((n' , _) , op' , _ , _ , _) with n ≟ℕ n' | op ≟op op'
          ≟× n op ((.n , _) , .op , _ , _ , _) | yes refl | yes refl =
            yes (refl , refl)
          ≟× n op ((_ , _) , _ , _ , _ , _) | no n≢n' | _  = no (n≢n' ∘ proj₁)
          ≟× n op ((_ , _) , _ , _ , _ , _) | _ | no op≢op' = no (op≢op' ∘ proj₂)
          h : Res → Maybe (List (EffectI × Op × Var × Var × Computation))
            → State (Tree V × ℕ) R
          h (just (inj₁ v)) es = ⟦ cv ⟧c (η [ x ↦ v ])
          h (just (inj₂ (n , op , v , κ))) nothing = return nothing
          h (just (inj₂ ((n , _) , op , v , κ))) (just es) with any (≟× n op) es
          h (just (inj₂ ((n , _) , op , v , κ))) (just es)
            | yes n,op∈es with find n,op∈es
          h (just (inj₂ ((n , _) , op , v , κ))) (just es)
            | yes n,op∈es | (n' , op' , x , k , c) , _ , _ , _ =
              ⟦ c ⟧c ((η [ x ↦ v ]) [ k ↦ ι→ κ ])
          h (just (inj₂ ((n , r) , op , v , κ))) (just es)
            | no n,op∉es = return (ιoper ((n , r) , op , v , λ v' → flip h (just es) ∘ ρres =<< κ v'))
          h nothing es = return nothing

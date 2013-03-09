-- An implementation of eff described in:
--  Programming with Algebraic Effects and Handlers
{-# OPTIONS --no-positivity-check --no-termination-check #-}
module eff where
open import Function using (_∘_; _$_)
open import Data.Bool hiding (if_then_else_)
open import Data.Empty
open import Data.List
open import Data.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Relation.Binary.Core using (Decidable; _≡_)
open import Relation.Nullary

data Var : Set where
_≟v_ : Decidable {A = Var} _≡_
x ≟v y = {!!}

data Const : Set where
data Op : Set where

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
    new_at_withc_end : EffectType → List OperationMap → Computation
                     → Computation
    withe_handle_end : Expr → Computation → Computation

Context = List (Var × Type)

import Data.List.Any
open Data.List.Any.Membership-≡

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

import Category.Monad
open import Category.Monad.State using (State; StateMonad)
open Category.Monad.RawMonad (StateMonad ℕ)

mutual
  data R : Set where
    ιv : V → R
    ιoper : ℕ × Op × V × (V → State ℕ R) → R
    nothing : R
  data V : Set where
    ιc : Const → V
    ιn : ℕ → V
    ιb : Bool → V
    ι⋆ : ⊤ → V
    ι× : V × V → V
    ι+ : V ⊎ V → V
    ι→ : (V → State ℕ R) → V
    ι⇒ : (R → State ℕ R) → V
    ιv : V ⊎ ℕ × Op × V × (V → R) → V
    nothing : V

ιres : Maybe (V ⊎ ℕ × Op × V × (V → State ℕ R)) → R
ιres (just (inj₁ v)) = ιv v
ιres (just (inj₂ oper)) = ιoper oper
ιres nothing = nothing

ρres : R → Maybe (V ⊎ ℕ × Op × V × (V → State ℕ R))
ρres (ιv v) = just (inj₁ v)
ρres (ιoper op) = just (inj₂ op)
ρres nothing = nothing

_† : (V → State ℕ R) → Maybe (V ⊎ ℕ × Op × V × (V → State ℕ R)) → State ℕ R
(f †) (just (inj₁ v)) = f v
(f †) (just (inj₂ (n , op , v , k))) =
  return (ιoper (n , op , v , λ v' → f † ∘ ρres =<< k v))
(f †) nothing = return nothing

Env = Var → V
_[_↦_] : Env → Var → V → Env
(η [ x ↦ v ]) y with x ≟v y
... | yes x≡y = v
... | no  x≢y = η y

mutual
  ⟦_⟧c_ : Computation → Env → State ℕ R
  ⟦ val e ⟧c η = return ∘ ιv =<< ⟦ e ⟧ η
  ⟦ letc x ≡ c₁ inn c₂ ⟧c η =
    ((λ v → ⟦ c₂ ⟧c (η [ x ↦ v ])) † ∘ ρres) =<< ⟦ c₁ ⟧c η
  ⟦ letrec f [ x ]≡ c₁ inn c₂ ⟧c η = {!!}
  ⟦ if e then c₁ else c₂ ⟧c η = elim-bool =<< ⟦ e ⟧ η
    where elim-bool : V → State ℕ R
          elim-bool (ιb true)  = ⟦ c₁ ⟧c η
          elim-bool (ιb false) = ⟦ c₂ ⟧c η
          elim-bool _ = return nothing
  ⟦ match e with⊥ ⟧c η = return nothing
  ⟦ match e left x ↦ c₁ right y ↦ c₂ ⟧c η = elim+ =<< ⟦ e ⟧ η
    where elim+ : V → State ℕ R
          elim+ (ι+ (inj₁ l)) = ⟦ c₁ ⟧c (η [ x ↦ l ])
          elim+ (ι+ (inj₂ r)) = ⟦ c₂ ⟧c (η [ y ↦ r ])
          elim+ _ = return nothing
  ⟦ match e withc x , y ↦ c ⟧c η = elim× =<< ⟦ e ⟧ η
    where elim× : V → State ℕ R
          elim× (ι× (v₀ , v₁)) = ⟦ c ⟧c (η [ x ↦ v₀ ] [ y ↦ v₁ ])
          elim× _ = return nothing
  ⟦ e₁ * e₂ ⟧c η = elim→ =<< ⟦ e₁ ⟧ η
    where elim→ : V → State ℕ R
          elim→ (ι→ f) = f =<< ⟦ e₂ ⟧ η
          elim→ _ = return nothing
  ⟦ new E ⟧c η = λ n → ιv (ιn n) , suc n
  ⟦ withe e handle c end ⟧c η = elim⇒ =<< ⟦ e ⟧ η
    where elim⇒ : V → State ℕ R
          elim⇒ (ι⇒ f) = f =<< ⟦ c ⟧c η
          elim⇒ _ = return nothing
  ⟦ new E at e withc ops end ⟧c η = {!!}
  
  ⟦_⟧_ : Expr → Env → State ℕ V
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
    where inj-oper : V → State ℕ V
          inj-oper (ιn n) =
            return $ ι→ (λ v → return $ ιoper (n , op , v , return ∘ ιv))
          inj-oper _ = return nothing
  ⟦ handler hs val xv ↦ cv finally x ↦ cf ⟧ η =
    return $ ι⇒ {!!}

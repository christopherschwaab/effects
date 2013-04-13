module testeff where
import Level
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary using (Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; decSetoid)
open import Relation.Nullary.Core

module choice where
  data OpChoice : Set where
    Choice : OpChoice
  _≟op_ : Decidable {A = OpChoice} _≡_
  Choice ≟op Choice = yes refl

  open import eff (decSetoid _≟op_)

  choice : Expr → OperationHandler
  choice c = c # Choice var 0 var 1 ↦ (var 1 * bool true)
  handlere : Expr → Expr
  handlere c = handler (choice c ∷ [])
                 val 0 ↦ val (var 0)
                 finally 0 ↦ val (var 0)
  
  go = proj₁ ((⟦
    letc 2 ≡ new (effect ((operation Choice ∶ unit ⟶ bool) ∷ []) end)
    inn (λ c → withe handlere c handle
                 (c # Choice) * tt
               end) (var 2) ⟧c
    (λ _ → blameV "empty env" 0)) emptyState)
  
  choose_all : Expr → OperationHandler
  choose_all c = c # Choice var 0 var 1 ↦
                  (letc 2 ≡ var 1 * bool true inn
                   letc 3 ≡ var 1 * bool false
                   inn val (var 2 , var 3))
  choose_all_handlere : Expr → Expr
  choose_all_handlere c = handler (choose_all c ∷ [])
                            val 0 ↦ val (var 0)
                            finally 0 ↦ val (var 0)
  go2 = proj₁ ((⟦
    letc 2 ≡ new (effect ((operation Choice ∶ unit ⟶ bool) ∷ []) end)
    inn (λ c → withe choose_all_handlere c handle
                 letc 3 ≡ (c # Choice) * tt
                 inn if var 3 then val (nat 10) else val (nat 20)
               end) (var 2) ⟧c
    (λ _ → blameV "empty env" 0)) emptyState)

module state where
  data OpChoice : Set where
    Lookup : OpChoice
    Update : OpChoice
  _≟op_ : Decidable {A = OpChoice} _≡_
  Lookup ≟op Lookup = yes refl
  Lookup ≟op Update = no λ()
  Update ≟op Update = yes refl
  Update ≟op Lookup = no λ()

  open import eff (decSetoid _≟op_)

  state : Type → Expr → Expr → Expr
  state S r x = handler
                (lookup ∷ update ∷ [])
                val 0 ↦ val (fun 1 ∶ S ↦ val (var 0))
                finally 0 ↦ val (var 0)
    where lookup : OperationHandler
          lookup = r # Lookup var 0 var 1 ↦
                     ((fun 0 ∶ S ↦ (var 1 * var 0)) * var 0)
          update : OperationHandler
          update = r # Update var 0 var 1 ↦
                     ((fun 0 ∶ S ↦ (var 1 * tt)) * var 0)

  ref = λ S → effect (
      (operation Lookup ∶ unit ⟶ S) ∷
      (operation Update ∶ S ⟶ unit) ∷ [])
    end

  go = proj₁ ((⟦
    letc 3 ≡ new (ref int)
    inn (λ r →
      withe state int r (nat 0) handle
        letc 20 ≡ (r # Update) * (nat 3) inn
        ((r # Lookup) * tt)
      end) (var 3) ⟧c
    (λ x → blameV "var not found: " x)) emptyState)

--  ref : Type → Expr → Expr
--  ref S x = new 

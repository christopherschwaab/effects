module testeff where
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)

open import eff

choice : Expr → OperationHandler
choice c = c # Choice var 0 var 1 ↦ (var 1 * bool true)
handlere : Expr → Expr
handlere c = handler (choice c ∷ [])
               val 0 ↦ val (var 0)
               finally 0 ↦ val (var 0)

go = proj₁ ((⟦
  letc 2 ≡ new (effect ((operation Choice ∶ unit ⟶ bool) ∷ []) end)
  inn (λ c → withe handlere c
               handle (c # Choice) * tt
             end) (var 2) ⟧c
  (λ _ → nothing)) emptyState)

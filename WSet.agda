module WSet where
open import Level
open import Function using (id)
open import Function.Equivalence renaming (id to eqid)
open import Data.Empty
open import Data.Product renaming (map to map×)
open import Data.Sum
open import Data.Unit using (⊤; tt)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_) renaming (refl to refl≡)
open import Relation.Nullary

record WSet {dc dℓ} c ℓ (DS : DecSetoid dc dℓ) : Set (suc (c ⊔ ℓ ⊔ dc ⊔ dℓ)) where
  open DecSetoid DS using (Carrier) renaming (_≈_ to _≋_)
  infix 4 _∈_ _≈_ _⊆_
  field
    Container : Set c
    _∈_ : Carrier → Container → Set ℓ
    insert : (y : Carrier) → (S : Container) → ∃ λ S' → ‌∀ a → a ∈ S' → a ≋ y ⊎ a ∈ S
    delete : (y : Carrier) → (S : Container) → ∃ λ S' → ∀ a → a ∈ S' → a ∈ S × ¬ a ≋ y
    _∪_ : (S₁ S₂ : Container) → ∃ λ S → ∀ a → a ∈ S → a ∈ S₁ ⊎ a ∈ S₂
    _∩_ : (S₁ S₂ : Container) → ∃ λ S → ∀ a → a ∈ S → a ∈ S₁ × a ∈ S₂
    _\\_ : (S₁ S₂ : Container) → ∃ λ S → ∀ a → a ∈ S → a ∈ S₁ × ¬ a ∈ S₂

  _≈_ : Container → Container → Set (ℓ ⊔ dc)
  _≈_ S S' = ∀ a → a ∈ S ⇔ a ∈ S'

  _⊆_ : Container → Container → Set (ℓ ⊔ dc)
  _⊆_ S S' = ∀ a → a ∈ S → a ∈ S'

  IsEmpty : Container → Set (ℓ ⊔ dc)
  IsEmpty S = ∀ a → ¬ a ∈ S
  
  isEquivalence : IsEquivalence _≈_
  isEquivalence = record
    { refl  = λ x → eqid
    ; sym   = λ e x → sym (e x)
    ; trans = λ e₁ e₂ x → e₂ x ∘ e₁ x }

listWSet : ∀{c} → (STO : StrictTotalOrder c c _) → WSet _ _ (StrictTotalOrder.decSetoid STO)
listWSet {c} STO = record
  { Container = SortedList
  ; _∈_ = λ x S → x ∈l proj₁ S
  ; insert = λ y S → insert y (proj₁ S) (proj₂ S)
  ; delete = λ y S → delete y (proj₁ S) (proj₂ S)
  ; _∪_ = λ S₁ S₂ → union (proj₁ S₁) (proj₂ S₁) (proj₁ S₂) (proj₂ S₂)
  ; _∩_ = λ S₁ S₂ → inter (proj₁ S₁) (proj₂ S₁) (proj₁ S₂) (proj₂ S₂)
  ; _\\_ = λ S₁ S₂ → diff (proj₁ S₁) (proj₂ S₁) (proj₁ S₂) (proj₂ S₂) } where
  open import Data.List
  open import Data.List.Any
  open StrictTotalOrder STO
  STOS = DecSetoid.setoid decSetoid
  open IsEquivalence (Setoid.isEquivalence STOS)
    using () renaming (refl to refl≈; sym to sym≈; trans to trans≈)

  IsSorted : List Carrier → Set c
  IsSorted [] = Lift ⊤
  IsSorted (x ∷ xs) = Lt x xs × IsSorted xs where
    Lt : Carrier → List Carrier → Set c
    Lt x₁ [] = Lift ⊤
    Lt x₁ (x₂ ∷ _) = x₁ < x₂
  SortedList = ∃ IsSorted

  open Membership STOS renaming (_∈_ to _∈l_)
  _∈_ : Carrier → SortedList → Set c
  x ∈ S = x ∈l proj₁ S
  
  NonEmptyList : SortedList → Set
  NonEmptyList ([] , _) = ⊥
  NonEmptyList _  = ⊤

  hd : (xs : SortedList) → NonEmptyList xs → Carrier
  hd ([] , _) ()
  hd (x ∷ xs , p) tt = x

  tl : (xs : SortedList) → NonEmptyList xs → SortedList
  tl ([] , _) ()
  tl (x ∷ xs , p) tt = xs , proj₂ p

  sorted : (xs : SortedList) → (ok : NonEmptyList xs) → ∀ a → a ∈ tl xs ok → hd xs ok < a
  sorted ([] , _) () _ _
  sorted (x ∷ [] , p) tt _ ()
  sorted (x₁ ∷ x₂ ∷ xs , x₁<x₂ , p) tt a (here a≈x₂) = proj₁ <-resp-≈ (sym≈ a≈x₂) x₁<x₂
  sorted (x₁ ∷ x₂ ∷ xs , x₁<x₂ , p) tt a (there a∈xs) =
    trans x₁<x₂ (sorted (x₂ ∷ xs , (proj₁ p) , proj₂ p) tt a a∈xs)

  unhere : ∀{x} → ∀ a → a ∈l [ x ] → a ≈ x
  unhere a (here a≈x) = a≈x
  unhere a (there ())

  insert : (y : Carrier)
         → (xs : List Carrier)
         → (S : IsSorted xs)
         → ∃ λ S' → ‌∀ a → a ∈ S' → a ≈ y ⊎ a ∈l xs
  insert y [] S[] = ([ y ] , S[] , S[]) , λ a a∈ → inj₁ (unhere a a∈)
  insert y (x ∷ xs) Sx with compare y x
  ... | tri< y<x y≉x x≮y = (y ∷ x ∷ xs , y<x , Sx) , prf where
    prf : ∀ a → a ∈l y ∷ x ∷ xs → a ≈ y ⊎ a ∈l x ∷ xs
    prf a (here a≈y)     = inj₁ a≈y
    prf a (there a∈x∷xs) = inj₂ a∈x∷xs
  ... | tri≈ y≮x y≈x x≮y = (x ∷ xs , Sx) , prf where
    prf : ∀ a → a ∈l x ∷ xs → a ≈ y ⊎ a ∈l x ∷ xs
    prf a (here a≈x)   = inj₁ (trans≈ a≈x (sym≈ y≈x))
    prf a (there a∈xs) = inj₂ (there a∈xs)
  ... | tri> y≮x y≉x x<y = ins (insert y xs (proj₂ Sx)) where
    ins : (∃ λ S' → ∀ a → a ∈l proj₁ S' → a ≈ y ⊎ a ∈l xs)
        → ∃ λ S' → ∀ a → a ∈l proj₁ S' → a ≈ y ⊎ a ∈l x ∷ xs
    ins (([] , S[]) , _) = ([ x ] , S[] , S[]) , λ a a∈ → inj₂ (here (unhere a a∈))
    ins ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
      x<z : z ≈ y ⊎ z ∈l xs → x < z
      x<z (inj₁ z≈y)  = proj₁ <-resp-≈ (sym≈ z≈y) x<y
      x<z (inj₂ z∈xs) = sorted (x ∷ xs , Sx) tt z z∈xs
      prf : ∀ a → a ∈l x ∷ z ∷ zs → a ≈ y ⊎ a ∈l x ∷ xs
      prf a (here a≈x) = inj₂ (here a≈x)
      prf a (there a∈) = h (IH a a∈) where
        h : a ≈ y ⊎ a ∈l xs → a ≈ y ⊎ a ∈l x ∷ xs
        h (inj₁ a≈y)  = inj₁ a≈y
        h (inj₂ a∈xs) = inj₂ (there a∈xs)

  delete : (y : Carrier)
         → (xs : List Carrier)
         → (S : IsSorted xs)
         → ∃ λ S' → ∀ a → a ∈ S' → a ∈l xs × ¬ a ≈ y
  delete y [] S[] = ([] , S[]) , λ a ()
  delete y (x ∷ xs) Sx with compare y x
  ... | tri< y<x y≉x x≮y = (x ∷ xs , Sx) , prf where
    prf : ∀ a → a ∈l x ∷ xs → a ∈l x ∷ xs × ¬ a ≈ y
    prf a (here a≈x)   = here a≈x , λ a≈y → y≉x (trans≈ (sym≈ a≈y) a≈x)
    prf a (there a∈xs) = there a∈xs , λ a≈y → x≮y (proj₁ <-resp-≈ a≈y (sorted (x ∷ xs , Sx) tt a a∈xs))
  ... | tri≈ y≮x y≈x x≮y = (xs , proj₂ Sx) , prf where
    prf : ∀ a → a ∈l xs → a ∈l x ∷ xs × ¬ a ≈ y
    prf a a∈xs = there a∈xs , λ a≈y → x≮y (proj₁ <-resp-≈ a≈y (sorted (x ∷ xs , Sx) tt a a∈xs))
  ... | tri> y≮x y≉x x<y = del (delete y xs (proj₂ Sx)) where
    del : (∃ λ S' → ∀ a → a ∈l proj₁ S' → a ∈l xs × ¬ a ≈ y)
        → ∃ λ S' → ∀ a → a ∈l proj₁ S' → a ∈l x ∷ xs × ¬ a ≈ y
    del (([] , S[]) , IH) = ([ x ] , S[] , S[])
                          , λ a a∈ → here (unhere a a∈)
                                   , λ a≈y → y≉x (trans≈ (sym≈ a≈y) (unhere a a∈))
    del ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
      x<z : (z ∈l xs × ¬ z ≈ y) → x < z
      x<z (z∈xs , z≉y) = sorted (x ∷ xs , Sx) tt z z∈xs
      prf : ∀ a → a ∈l x ∷ z ∷ zs → a ∈l x ∷ xs × ¬ a ≈ y
      prf a (here a≈x) = here a≈x , (λ a≈y → y≉x (trans≈ (sym≈ a≈y) a≈x))
      prf a (there a∈) = h (IH a a∈) where
        h : a ∈l xs × ¬ a ≈ y → a ∈l x ∷ xs × ¬ a ≈ y
        h (a∈xs , a≉y) = there a∈xs , a≉y

  mutual
    union : (xs : List Carrier)
          → (Sx : IsSorted xs)
          → (ys : List Carrier)
          → (Sy : IsSorted ys)
          → ∃ λ S → ∀ a → a ∈ S → a ∈l xs ⊎ a ∈l ys
    union [] S[] = λ ys Sy → (ys , Sy) , λ a a∈ys → inj₂ a∈ys
    union (x ∷ xs) Sx  = union' x xs Sx

    union' : (x : Carrier)
           → (xs : List Carrier)
           → (Sx : IsSorted (x ∷ xs))
           → (ys : List Carrier)
           → (Sy : IsSorted ys)
           → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs ⊎ a ∈l ys
    union' x xs Sx [] S[] = (x ∷ xs , Sx) , λ a a∈xs → inj₁ a∈xs
    union' x xs Sx (y ∷ ys) Sy with compare y x
    ... | tri< y<x y≉x x≮y = u (union' x xs Sx ys (proj₂ Sy)) where
      u : (∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs ⊎ a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
      u (([] , S[]) , IH) = ([ y ] , S[] , S[]) , λ a a∈ → inj₂ (here (unhere a a∈))
      u ((z ∷ zs , Sz) , IH) = (y ∷ z ∷ zs , y<z (IH z (here refl≈)) , Sz) , prf where
        y<z : z ∈l x ∷ xs ⊎ z ∈l ys → y < z
        y<z (inj₂ z∈ys) = sorted (y ∷ ys , Sy) tt z z∈ys
        y<z (inj₁ (here z≈x))   = proj₁ <-resp-≈ (sym≈ z≈x) y<x
        y<z (inj₁ (there z∈xs)) = trans y<x (sorted (x ∷ xs , Sx) tt z z∈xs)
        prf : ∀ a → a ∈l y ∷ z ∷ zs → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
        prf a (here a≈y) = inj₂ (here a≈y)
        prf a (there a∈) = h (IH a a∈) where
          h : a ∈l x ∷ xs ⊎ a ∈l ys → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
          h (inj₂ a∈ys) = inj₂ (there a∈ys)
          h (inj₁ a∈) = inj₁ a∈
    ... | tri≈ y≮x y≈x x≮y = u (union xs (proj₂ Sx) ys (proj₂ Sy)) where
      u : (∃ λ S → ∀ a → a ∈ S → a ∈l xs ⊎ a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
      u (([] , S[]) , IH) = ([ x ] , S[] , S[]) , λ a a∈ → inj₁ (here (unhere a a∈))
      u ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
        x<z : z ∈l xs ⊎ z ∈l ys → x < z
        x<z (inj₁ z∈xs) = sorted (x ∷ xs , Sx) tt z z∈xs
        x<z (inj₂ z∈ys) = proj₂ <-resp-≈ y≈x (sorted (y ∷ ys , Sy) tt z z∈ys)
        prf : ∀ a → a ∈l x ∷ z ∷ zs → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
        prf a (here a≈x) = inj₁ (here a≈x)
        prf a (there a∈) = h (IH a a∈) where
          h : a ∈l xs ⊎ a ∈l ys → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
          h (inj₁ a∈xs) = inj₁ (there a∈xs)
          h (inj₂ a∈ys) = inj₂ (there a∈ys)
    ... | tri> y≮x y≉x x<y = u (union xs (proj₂ Sx) (y ∷ ys) Sy) where
      u : (∃ λ S → ∀ a → a ∈ S → a ∈l xs ⊎ a ∈l y ∷ ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
      u (([] , S[]) , IH) = ([ x ] , S[] , S[]) , λ a a∈ → inj₁ (here (unhere a a∈))
      u ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
        x<z : z ∈l xs ⊎ z ∈l y ∷ ys → x < z
        x<z (inj₁ z∈xs) = sorted (x ∷ xs , Sx) tt z z∈xs
        x<z (inj₂ (here z≈y))   = proj₁ <-resp-≈ (sym≈ z≈y) x<y
        x<z (inj₂ (there z∈ys)) = trans x<y (sorted (y ∷ ys , Sy) tt z z∈ys)
        prf : ∀ a → a ∈l x ∷ z ∷ zs → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
        prf a (here a≈x) = inj₁ (here a≈x)
        prf a (there a∈) = h (IH a a∈) where
          h : a ∈l xs ⊎ a ∈l y ∷ ys → a ∈l x ∷ xs ⊎ a ∈l y ∷ ys
          h (inj₁ a∈xs) = inj₁ (there a∈xs)
          h (inj₂ a∈) = inj₂ a∈

  mutual
    inter : (xs : List Carrier)
          → (Sx : IsSorted xs)
          → (ys : List Carrier)
          → (Sy : IsSorted ys)
          → ∃ λ S → ∀ a → a ∈ S → a ∈l xs × a ∈l ys
    inter [] S[] = λ ys Sy → ([] , S[]) , λ a ()
    inter (x ∷ xs) Sx  = inter' x xs Sx

    inter' : (x : Carrier)
           → (xs : List Carrier)
           → (Sx : IsSorted (x ∷ xs))
           → (ys : List Carrier)
           → (Sy : IsSorted ys)
          → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × a ∈l ys
    inter' x xs Sx [] S[] = ([] , S[]) , λ a ()
    inter' x xs Sx (y ∷ ys) Sy with compare y x
    ... | tri< y<x y≉x x≮y = i (inter xs (proj₂ Sx) (y ∷ ys) Sy) where
      i : (∃ λ S → ∀ a → a ∈ S → a ∈l xs × a ∈l y ∷ ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × a ∈l y ∷ ys
      i (([] , S[]) , IH) = ([] , S[]) , λ a ()
      i ((z ∷ zs , Sz) , IH) = (z ∷ zs , Sz) , λ a a∈ → map× there id (IH a a∈)
    ... | tri≈ y≮x y≈x x≮y = i (inter xs (proj₂ Sx) ys (proj₂ Sy)) where
      i : (∃ λ S → ∀ a → a ∈ S → a ∈l xs × a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × a ∈l y ∷ ys
      i (([] , S[]) , IH) = ([ x ] , S[] , S[])
                          , λ a a∈ → here (unhere a a∈)
                                   , here (trans≈ (unhere a a∈) (sym≈ y≈x))
      i ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
        x<z : z ∈l xs × z ∈l ys → x < z
        x<z (z∈xs , z∈ys) = sorted (x ∷ xs , Sx) tt z z∈xs
        prf : ∀ a → a ∈l x ∷ z ∷ zs → a ∈l x ∷ xs × a ∈l y ∷ ys
        prf a (here a≈x) = here a≈x , here (trans≈ a≈x (sym≈ y≈x))
        prf a (there a∈) = map× there there (IH a a∈)
    ... | tri> y≮x y≉x x<y = i (inter' x xs Sx ys (proj₂ Sy)) where
      i : (∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × a ∈l y ∷ ys
      i (([] , S[]) , IH) = ([] , S[]) , λ a ()
      i ((z ∷ zs , Sz) , IH) = (z ∷ zs , Sz) , λ a a∈ → map× id there (IH a a∈)

  mutual
    diff : (xs : List Carrier)
          → (Sx : IsSorted xs)
          → (ys : List Carrier)
          → (Sy : IsSorted ys)
          → ∃ λ S → ∀ a → a ∈ S → a ∈l xs × ¬ a ∈l ys
    diff [] S[] = λ ys Sy → ([] , S[]) , λ a ()
    diff (x ∷ xs) Sx = diff' x xs Sx
    
    diff' : (x : Carrier)
          → (xs : List Carrier)
          → (Sx : IsSorted (x ∷ xs))
          → (ys : List Carrier)
          → (Sy : IsSorted ys)
          → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × ¬ a ∈l ys
    diff' x xs Sx [] S[] = (x ∷ xs , Sx) , λ a a∈ → a∈ , λ()
    diff' x xs Sx (y ∷ ys) Sy with compare y x
    ... | tri< y<x y≉x x≮y = d (diff' x xs Sx ys (proj₂ Sy)) where
      d : (∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × ¬ a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × ¬ a ∈l y ∷ ys
      d (([] , S[]) , IH) = ([] , S[]) , λ a ()
      d ((z ∷ zs , Sz) , IH) = (z ∷ zs , Sz)
                             , λ a a∈ → proj₁ (IH a a∈) , prf a (IH a a∈) where
        prf : ∀ a → a ∈l x ∷ xs × ¬ a ∈l ys → ¬ a ∈l y ∷ ys
        prf a (here a≈x , a∉ys) (here a≈y)  = y≉x (trans≈ (sym≈ a≈y) a≈x)
        prf a (there a∈xs , a∉ys) (here a≈y) = x≮y (proj₁ <-resp-≈ a≈y (sorted (x ∷ xs , Sx) tt a a∈xs))
        prf a (a∈ , a∉ys) (there a∈ys) = a∉ys a∈ys
    ... | tri≈ y≮x y≈x x≮y = d (diff xs (proj₂ Sx) ys (proj₂ Sy)) where
      d : (∃ λ S → ∀ a → a ∈ S → a ∈l xs × ¬ a ∈l ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × ¬ a ∈l y ∷ ys
      d (([] , S[]) , IH) = ([] , S[]) , λ a ()
      d ((z ∷ zs , Sz) , IH) = (z ∷ zs , Sz)
                             , λ a a∈ → there (proj₁ (IH a a∈)) , contr a (IH a a∈) where
        contr : ∀ a → a ∈l xs × ¬ a ∈l ys → ¬ a ∈l y ∷ ys
        contr a (a∈xs , a∉ys) (here a≈y) = x≮y (proj₁ <-resp-≈ a≈y (sorted (x ∷ xs , Sx) tt a a∈xs))
        contr a (a∈xs , a∉ys) (there a∈ys) = a∉ys a∈ys
    ... | tri> y≮x y≉x x<y = d (diff xs (proj₂ Sx) (y ∷ ys) Sy) where
      d : (∃ λ S → ∀ a → a ∈ S → a ∈l xs × ¬ a ∈l y ∷ ys)
        → ∃ λ S → ∀ a → a ∈ S → a ∈l x ∷ xs × ¬ a ∈l y ∷ ys
      d (([] , S[]) , IH) = ([ x ] , S[] , S[]) , λ a a∈ → here (unhere a a∈) , contr a (unhere a a∈) where
        contr : ∀ a → a ≈ x → ¬ a ∈l y ∷ ys
        contr a a≈x (here a≈y)   = y≉x (trans≈ (sym≈ a≈y) a≈x)
        contr a a≈x (there a∈ys) = y≮x (proj₁ <-resp-≈ a≈x (sorted (y ∷ ys , Sy) tt a a∈ys))
      d ((z ∷ zs , Sz) , IH) = (x ∷ z ∷ zs , x<z (IH z (here refl≈)) , Sz) , prf where
        x<z : z ∈l xs × ¬ z ∈l y ∷ ys → x < z
        x<z (z∈xs , z∉) = sorted (x ∷ xs , Sx) tt z z∈xs
        prf : ∀ a → a ∈l x ∷ z ∷ zs → a ∈l x ∷ xs × ¬ a ∈l y ∷ ys
        prf a (here a≈x) = here a≈x , h where
          h : ¬ a ∈l y ∷ ys
          h (here a≈y)   = y≉x (trans≈ (sym≈ a≈y) a≈x)
          h (there a∈ys) = y≮x (proj₁ <-resp-≈ a≈x (sorted (y ∷ ys , Sy) tt a a∈ys))
        prf a (there a∈) = map× there id (IH a a∈)

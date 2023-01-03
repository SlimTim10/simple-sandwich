{-# OPTIONS --without-K --safe #-}

-- ⊔ "\lub" (least upper bound, basically maximum)
-- 𝓤 "\MCU"
open import Agda.Primitive
  using (Level ; lzero ; lsuc ; _⊔_)
  renaming (Set to 𝓤)
  public

-- We can use Type or 𝓤 where it makes sense
Type = Set

-- Empty type
-- 𝟘 "\b0"
data 𝟘 : Type where

-- Unit type
-- 𝟙 "\b1"
record 𝟙 : Type where
  constructor
    ⋆

-- Let i, j, and k range over universe levels
variable i j k : Level

-- General sigma type with universes
-- Σ "\Sigma"
record Σ {A : 𝓤 i} (B : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
infixr 1 _,_

-- i, j, k are not mentioned in the definition, but they are implicit parameters.
-- Everything declared with a variable becomes an implicit parameter, in the order that it is used.
Sigma : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
Sigma {i} {j} A B = Σ {i} {j} {A} B

-- Sigma notation
-- ꞉ "\: 4"
syntax Sigma A (λ x → b) = Σ x ꞉ A , b

infix -1 Sigma

-- Pi type
Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

-- For special colon, type "\:4"
syntax Pi A (λ x → b) = Π x ꞉ A , b

-- Conjunction
-- × "\x"
_×_ : 𝓤 i → 𝓤 j → 𝓤 (i ⊔ j)
A × B = Σ x ꞉ A , B

infixr 2 _×_

-- Disjunction
-- ∔ "\.+"
data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B

infixr 20 _∔_

-- Negation
-- ¬ "\neg"
¬_ : 𝓤 i → 𝓤 i
¬ A = A → 𝟘

-- Identity
-- ≡ "\=="
data _≡_ {X : 𝓤 i} : X → X → 𝓤 i where
  refl : (x : X) → x ≡ x

infix 0 _≡_

-- ≢ "\==n"
_≢_ : {X : 𝓤 i} → X → X → 𝓤 i
x ≢ y = ¬ (x ≡ y)

-- \bN
data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_≤_ : ℕ → ℕ → Type
0 ≤ y = 𝟙
suc x ≤ 0 = 𝟘
suc x ≤ suc y = x ≤ y

_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

module _
  {A : Type}
  {B : A → Type}
  where
  
  _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  f ∼ g = Π x ꞉ A , (f x ≡ g x)
  -- f ∼ g = ∀ x → f x ≡ g x

  infix 0 _∼_ -- low precedence

_∘_ : {A B : Type} {C : B → Type}
  → ((y : B) → C y)
  → (f : A → B)
  → (x : A) → C (f x)
g ∘ f = λ x → g (f x)

id : {X : Type} → X → X
id x = x

record is-bijection {A B : Type} (f : A → B) : Type where
  constructor
    Inverse
  field
    inverse : B → A
    η : inverse ∘ f ∼ id
    ε : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
  constructor
    Isomorphism
  field
    bijection : A → B
    bijectivity : is-bijection bijection

infix 0 _≅_


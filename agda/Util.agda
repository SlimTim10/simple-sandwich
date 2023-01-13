{-# OPTIONS --without-K #-}

open import Agda.Primitive
  using ()
  renaming (Set to Type)
  public

-- Empty type
-- 𝟘 "\b0"
data 𝟘 : Type where

-- Unit type
-- 𝟙 "\b1"
record 𝟙 : Type where
  constructor
    ⋆

-- Sigma type (dependent sum)
-- Σ "\Sigma"
record Σ {A : Type} (B : A → Type) : Type where
  constructor
    _,_
  field
    pr₁ : A
    pr₂ : B pr₁

open Σ public
infixr 0 _,_

Sigma : (A : Type) (B : A → Type) → Type
Sigma A B = Σ {A} B

-- ꞉ "\:4"
syntax Sigma A (λ x → b) = Σ x ꞉ A , b
infix -1 Sigma

-- Pi type (dependent product)
Pi : (A : Type) (B : A → Type) → Type
Pi A B = (x : A) → B x

-- ꞉ "\:4"
syntax Pi A (λ x → b) = Π x ꞉ A , b

-- Non-dependent pair, AKA cartesian product, AKA conjunction
-- × "\x"
_×_ : Type → Type → Type
A × B = Σ x ꞉ A , B

infixr 2 _×_

-- Binary sum, AKA disjoint union, AKA disjunction
-- ∔ "\.+"
data _∔_ (A B : Type) : Type where
  inl : A → A ∔ B
  inr : B → A ∔ B

infixr 20 _∔_

-- Negation
-- ¬ "\neg"
¬_ : Type → Type
¬ A = A → 𝟘

infix 1000 ¬_

-- Identity
-- ≡ "\=="
data _≡_ {A : Type} : A → A → Type where
  refl : (x : A) → x ≡ x

infix 0 _≡_

-- ≢ "\==n"
_≢_ : {X : Type} → X → X → Type
x ≢ y = ¬ (x ≡ y)

-- Natural numbers
-- ℕ "\bN"
data ℕ : Type where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- ≤ "\<="
_≤_ : ℕ → ℕ → Type
0 ≤ y = 𝟙
suc x ≤ 0 = 𝟘
suc x ≤ suc y = x ≤ y

-- ≥ "\>="
_≥_ : ℕ → ℕ → Type
x ≥ y = y ≤ x

module _
  {A : Type}
  {B : A → Type}
  where

  -- Homotopy
  _∼_ : (Π x ꞉ A , B x) → (Π x ꞉ A , B x) → Type
  f ∼ g = Π x ꞉ A , (f x ≡ g x)
  -- _∼_ : ((x : A) → B x) → ((x : A) → B x) → Type
  -- f ∼ g = ∀ x → f x ≡ g x

  infix 0 _∼_ -- low precedence

-- Function composition
-- ∘ "\o"
_∘_
  : {A B : Type} {C : B → Type}
  → (Π y ꞉ B , C y)
  → (f : A → B)
  → Π x ꞉ A , C (f x)
(g ∘ f) x = g (f x)

id : {X : Type} → X → X
id x = x

-- Isomorphism
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

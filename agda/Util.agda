{-# OPTIONS --without-K #-}

open import Agda.Primitive
  using ()
  renaming (Set to Type)
  public

-- Empty type
-- ð "\b0"
data ð : Type where

-- Unit type
-- ð "\b1"
record ð : Type where
  constructor
    â

-- Sigma type (dependent sum)
-- Î£ "\Sigma"
record Î£ {A : Type} (B : A â Type) : Type where
  constructor
    _,_
  field
    prâ : A
    prâ : B prâ

open Î£ public
infixr 0 _,_

Sigma : (A : Type) (B : A â Type) â Type
Sigma A B = Î£ {A} B

-- ê "\:4"
syntax Sigma A (Î» x â b) = Î£ x ê A , b
infix -1 Sigma

-- Pi type (dependent product)
Pi : (A : Type) (B : A â Type) â Type
Pi A B = (x : A) â B x

-- ê "\:4"
syntax Pi A (Î» x â b) = Î  x ê A , b

-- Non-dependent pair, AKA cartesian product, AKA conjunction
-- Ã "\x"
_Ã_ : Type â Type â Type
A Ã B = Î£ x ê A , B

infixr 2 _Ã_

-- Binary sum, AKA disjoint union, AKA disjunction
-- â "\.+"
data _â_ (A B : Type) : Type where
  inl : A â A â B
  inr : B â A â B

infixr 20 _â_

-- Negation
-- Â¬ "\neg"
Â¬_ : Type â Type
Â¬ A = A â ð

infix 1000 Â¬_

-- Identity
-- â¡ "\=="
data _â¡_ {A : Type} : A â A â Type where
  refl : (x : A) â x â¡ x

infix 0 _â¡_

-- â¢ "\==n"
_â¢_ : {X : Type} â X â X â Type
x â¢ y = Â¬ (x â¡ y)

-- Natural numbers
-- â "\bN"
data â : Type where
  zero : â
  suc : â â â

{-# BUILTIN NATURAL â #-}

-- â¤ "\<="
_â¤_ : â â â â Type
0 â¤ y = ð
suc x â¤ 0 = ð
suc x â¤ suc y = x â¤ y

-- â¥ "\>="
_â¥_ : â â â â Type
x â¥ y = y â¤ x

module _
  {A : Type}
  {B : A â Type}
  where

  -- Homotopy
  _â¼_ : (Î  x ê A , B x) â (Î  x ê A , B x) â Type
  f â¼ g = Î  x ê A , (f x â¡ g x)
  -- _â¼_ : ((x : A) â B x) â ((x : A) â B x) â Type
  -- f â¼ g = â x â f x â¡ g x

  infix 0 _â¼_ -- low precedence

-- Function composition
-- â "\o"
_â_
  : {A B : Type} {C : B â Type}
  â (Î  y ê B , C y)
  â (f : A â B)
  â Î  x ê A , C (f x)
(g â f) x = g (f x)

id : {X : Type} â X â X
id x = x

-- Isomorphism
record is-bijection {A B : Type} (f : A â B) : Type where
  constructor
    Inverse
  field
    inverse : B â A
    Î· : inverse â f â¼ id
    Îµ : f â inverse â¼ id

record _â_ (A B : Type) : Type where
  constructor
    Isomorphism
  field
    bijection : A â B
    bijectivity : is-bijection bijection

infix 0 _â_

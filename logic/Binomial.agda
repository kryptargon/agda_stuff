module Binomial where

------------------------------EQUALITY----------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x
-- Reflexivity means equality
infixl 2 _≡_

trans : ∀ {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    --------  x ≡ y ∧ y ≡ z → x ≡ z
    → x ≡ z
trans refl refl = refl  -- proof that equality is transitive

sym : ∀ {A : Set} {x y : A}
    → x ≡ y
    --------  x ≡ y → y ≡ x
    → y ≡ x
sym refl = refl         -- proof that equality is symmetric

cong : ∀ {A B : Set} (f : A → B) {x y : A}
    → x ≡ y
    ----------- x ≡ y → f(x) ≡ f(y)
    → f x ≡ f y
cong f refl = refl      -- proof that equality satisfies congruence

module ≡-Reasoning {B : Set} where

    infix  1 begin_
    infixr 2 _≡⟨_⟩_
    infix  3 _∎-qed

    begin_ : ∀ {x y : B}          -- start reasoning
        → x ≡ y
        -------
        → x ≡ y
    begin x≡y = x≡y

    _≡⟨_⟩_ : ∀ (x : B) {y z : B}  -- transitive deduction
        → x ≡ y
        → y ≡ z
        -------
        → x ≡ z
    x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

    _∎-qed : ∀ (x : B)            -- q.e.d. (deduced reflexivity)
        -------
        → x ≡ x
    x ∎-qed = refl

open ≡-Reasoning

------------------------------NUMBERS AND OPERATIONS--------------------------------

data Number : Set where
    num : Number             -- at least some Number exists

data Term : Set where
    `   : Number → Term      -- a Number is a Term
    _+_ : Term → Term → Term -- addition of 2 Terms is a Term
    _*_ : Term → Term → Term -- multiplication of 2 Terms is a Term
infixl 6  _+_
infixl 7  _*_

_² : Term → Term  -- abbreviation for squaring
a ² = a * a

2×_ : Term → Term -- abbreviation for doubling
2× a = a + a

------------------------------NECESSARY RULES---------------------------------------

postulate
    assoc+  : ∀ {a b c : Term}  → (a + b) + c ≡ a + (b + c)
    assoc*  : ∀ {a b c : Term}  → (a * b) * c ≡ a * (b * c)
    comm+   : ∀ {a b : Term}    →       a + b ≡ b + a
    comm*   : ∀ {a b : Term}    →       a * b ≡ b * a
    distr   : ∀ {a b c : Term}  → (a + b) * c ≡ (a * c) + (b * c)

------------------------------PROOF OF BINOMIAL FORMULA-----------------------------

binom : ∀ {a b : Term} → (a + b) ² ≡ (a ² + (2× (a * b) + b ²))

binom {a} {b} = begin                   (a + b) ²
    ≡⟨ refl ⟩                           (a + b) * (a + b)
    ≡⟨ distr ⟩                          (a * (a + b))   + (b * (a + b))
    ≡⟨ cong (_+ b * (a + b)) comm* ⟩    ((a + b) * a)   + (b * (a + b))
    ≡⟨ cong (_+ b * (a + b)) distr ⟩    (a * a + b * a) + (b * (a + b))
    ≡⟨ refl ⟩                           (a ²   + b * a) + (b * (a + b))
    ≡⟨ cong ((a ² + b * a) +_) comm* ⟩  (a ²   + b * a) + ((a + b) * b)
    ≡⟨ cong ((a ² + b * a) +_) distr ⟩  (a ²   + b * a) + (a * b + b * b)
    ≡⟨ assoc+ ⟩                         a ² +  (b * a + (a * b + b * b))
    ≡⟨ cong (a ² +_) (sym assoc+) ⟩     a ² + ((b * a + a * b) + b * b)
    ≡⟨ cong (a ² +_) refl ⟩             a ² + ((b * a + a * b) + b ²)
    ≡⟨ cong (a ² +_)
      (cong (_+ b ²)
      (cong (_+ (a * b)) comm*)) ⟩      a ² + ((a * b + a * b) + b ²)
    ≡⟨ cong (a ² +_)
      (cong (_+ b ²) refl) ⟩            a ² + (2× (a * b) + b ²)    ∎-qed
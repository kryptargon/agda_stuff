module Integers where

------------------------------EQUALITY----------------------------------------------

data _≡_ {A : Set} (x : A) : A → Set where
    refl : x ≡ x
-- Reflexivity means equality
infixl 2 _≡_

trans : ∀ {A : Set} {x y z : A}
    → x ≡ y
    → y ≡ z
    --------
    → x ≡ z
trans refl refl = refl  -- proof that equality is transitive

sym : ∀ {A : Set} {x y : A}
    → x ≡ y
        -----
    → y ≡ x
sym refl = refl         -- proof that equality is symmetric

cong : ∀ {A B : Set} (f : A → B) {x y : A}
    → x ≡ y
    -----------
    → f x ≡ f y
cong f refl = refl      -- proof that equality satisfies congruence

module ≡-Reasoning {B : Set} where

    infix  1 begin_
    infixr 2 _≡⟨_⟩_
    infix  3 _∎

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

    _∎ : ∀ (x : B)                -- qed (reflexivity proven)
        -------
        → x ≡ x
    x ∎ = refl

open ≡-Reasoning

----------------------------INEQUALITY----------------------------------------------

data ⊥ : Set where
    ---- ⊥ is unconstructable

¬_ : Set → Set
¬ a = (a → ⊥)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)
infixl 2 _≢_

------------------------------EXISTENCE and DECIDABILITY----------------------------

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B
∃-syntax : ∀ {A : Set} → (A → Set) → Set
∃-syntax = Σ _
syntax ∃-syntax (λ x → B) = ∃[ x ] B

data Dec (A : Set) : Set where
    yes :   A → Dec A
    no  : ¬ A → Dec A

------------------------------NUMBERS AND OPERATIONS--------------------------------

data ℕ : Set where
    zero : ℕ        -- zero ∈ ℕ
    suc  : ℕ → ℕ    -- ∀ n ∈ ℕ : (suc n) ∈ ℕ

one = suc zero

_+ⁿ_ : ℕ → ℕ → ℕ
zero  +ⁿ b = b
suc a +ⁿ b = suc (a +ⁿ b)

_∸ⁿ_ : ℕ → ℕ → ℕ
zero ∸ⁿ b = b
suc a ∸ⁿ zero = suc a
suc a ∸ⁿ suc b = a ∸ⁿ b  

_*ⁿ_ : ℕ → ℕ → ℕ
zero *ⁿ b = zero
suc a *ⁿ b = a +ⁿ (a *ⁿ b)

data _≤ⁿ_ : ℕ → ℕ → Set where
    z≤z : ∀ {n : ℕ}             → zero ≤ⁿ n
    s≤s : ∀ {m n : ℕ} → m ≤ⁿ n  → suc m ≤ⁿ suc n

_≤ⁿ?_ : ∀ (a b : ℕ) → Dec (a ≤ⁿ b)
zero ≤ⁿ? b = yes z≤z
suc a ≤ⁿ? zero = no (λ ())
suc a ≤ⁿ? suc b with a ≤ⁿ? b
... | yes a≤b = yes (s≤s a≤b)
... | no  a≰b = no λ {(s≤s a≤b) → a≰b a≤b}

data ℤ : Set where
    pos : ℕ → ℤ     -- ∀ n ∈ ℕ : (pos n) ∈ ℤ
    neg : ℕ → ℤ     -- ∀ n ∈ ℕ : (neg n) ∈ ℤ

_+ᶻ_ : ℤ → ℤ → ℤ
pos a +ᶻ pos b = pos (a +ⁿ b)
pos a +ᶻ neg b with a ≤ⁿ? b
... | yes a≤b  = neg (b ∸ⁿ a)
... | no  a≰b  = pos (a ∸ⁿ b)
neg a +ᶻ pos b = (pos b +ᶻ neg a)
neg a +ᶻ neg b = neg (a +ⁿ b)

_*ᶻ_ : ℤ → ℤ → ℤ
pos a *ᶻ pos b = pos (a *ⁿ b)
pos a *ᶻ neg b = neg (a *ⁿ b)
neg a *ᶻ pos b = neg (a *ⁿ b)
neg a *ᶻ neg b = pos (a *ⁿ b)
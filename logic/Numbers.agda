module Numbers where
-- https://agda.github.io/agda-stdlib/Data.Integer.Base.html
-- https://agda.github.io/agda-stdlib/Data.Rational.Base
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

record _∧_ (A : Set) (B : Set) : Set where
    constructor _,_
    field
        fst : A
        snd : B
infixl 3 _∧_
------------------------------NATURALS----------------------------------------------

data ℕ : Set where
    zero : ℕ        -- zero ∈ ℕ
    suc  : ℕ → ℕ    -- ∀ n ∈ ℕ : (suc n) ∈ ℕ
    
0ℕ = zero
1ℕ = suc 0ℕ
2ℕ = suc 1ℕ
3ℕ = suc 2ℕ
4ℕ = suc 3ℕ
--- ....

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

_<ⁿ_ : ℕ → ℕ → Set
a <ⁿ b = suc a ≤ⁿ b

_<ⁿ?_ : ∀ (a b : ℕ) → Dec (a <ⁿ b)
a <ⁿ? b = suc a ≤ⁿ? b

------------------------------INTEGERS----------------------------------------------

data ℤ : Set where
    +[_]   : ∀ (n : ℕ) → ℤ      -- if n ∈ ℕ, then n ∈ ℤ
    -[1+_] : ∀ (n : ℕ) → ℤ      -- if n ∈ ℕ, then -(1+n) ∈ ℤ

pattern +0       = +[ zero ]
pattern +[1+_] n = +[ suc n ]

0ℤ = +0
1ℤ = +[1+ 0ℕ ]  -- = +[ 1ℕ ]
2ℤ = +[1+ 1ℕ ]
3ℤ = +[1+ 2ℕ ]
--- ....
-1ℤ = -[1+ 0ℕ ]
-2ℤ = -[1+ 1ℕ ]
-3ℤ = -[1+ 2ℕ ]
-4ℤ = -[1+ 3ℕ ]
--- ....


∥_∥ : ℤ → ℕ
∥ -[1+ n ] ∥ = suc n
∥  +[ n ]  ∥ = n

-ᶻ_ : ℤ → ℤ
-ᶻ -[1+ n ] = +[1+ n ]
-ᶻ       +0 = +0
-ᶻ +[1+ n ] = -[1+ n ]

_-ⁿ_ : ℕ → ℕ → ℤ
a -ⁿ b with a ≤ⁿ? b
... | yes a≤b = -ᶻ +[ a ∸ⁿ b ]
... | no  a≰b =    +[ a ∸ⁿ b ]

_+ᶻ_ :  ℤ → ℤ → ℤ
+[ a ]   +ᶻ +[ b ]   = +[ a +ⁿ b ]
+[ a ]   +ᶻ -[1+ b ] = a -ⁿ (suc b)
-[1+ a ] +ᶻ +[ b ]   = b -ⁿ (suc a)
-[1+ a ] +ᶻ -[1+ b ] = -[1+ suc (a +ⁿ b) ]

_*ᶻ_ : ℤ → ℤ → ℤ
+[ a ]   *ᶻ +[ b ]   = +[ a *ⁿ b ]
+[ a ]   *ᶻ -[1+ b ] = -[1+ (a *ⁿ (suc b)) ]
-[1+ a ] *ᶻ +[ b ]   = -[1+ ((suc a) *ⁿ b) ]
-[1+ a ] *ᶻ -[1+ b ] = +[ (suc a) *ⁿ (suc b) ]

----------------------------DIVISIBILITY AND RATIONALS------------------------------

data _∥_ : ℕ → ℕ → Set where
    [_×_≡_] : ∀ {a b c : ℕ} → a *ⁿ b ≡ c → (c ∥ a)
infixl 5 _∥_

data Coprime[_,_] : ℕ → ℕ → Set where
    [_≁_] : ∀ {a b i : ℕ} → (((a ∥ i) ∧ (b ∥ i)) → i ≡ 1ℕ) → Coprime[ a , b ]

record ℚ : Set where
    constructor mkℚ
    field
        numerator : ℤ
        denominator-1 : ℕ
        .isCoprime : Coprime[ ∥ numerator ∥ , suc denominator-1 ]
    -- rational numbers can only be constructed *uniquely*
    -- when the numerator and denominator are relatively prime
    denominator : ℤ
    denominator = +[ suc denominator-1 ]
open ℚ public using ()
    renaming (numerator to ↥_; denominator to ↧_)

_≅_ : ℚ → ℚ → Set
p ≅ q = ((↥ p) *ᶻ (↧ q)) ≡ ((↥ q) *ᶻ (↧ p))

mod : (a b c d : ℕ) → ℕ
mod a b zero d = a
mod a b (suc c) zero = mod zero b c b
mod a b (suc c) (suc d) = mod (suc a) b c d

data ℕ+ : ℕ → Set where
    pos : ∀ {n : ℕ} → ℕ+ (suc n)
    -- enforce n > 0

_%_ : (m n : ℕ) {_ : ℕ+ n} → ℕ
m % suc n = mod 0ℕ n m n

m%n<n : ∀ m n .{{_ : ℕ+ n}} → (m % n) <ⁿ n
m%n<n m (suc n) = s≤s {!   !}

-- gcd : ∀ (m n : ℕ) → (suc n) ≤ⁿ m → ℕ
-- gcd m zero _ = m
-- gcd m (suc n) n<m = gcd n (m % (suc n)) {! m%n<n  !}
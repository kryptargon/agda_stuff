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
    zero : Number             -- at least some Number exists
    suc : Number → Number     -- if n is a Number, (suc n) is another Number

one = suc zero
two = suc one
three = suc two
four = suc two

data Term : Set where
    `   : Number → Term      -- a Number is a Term
    _+_ : Term → Term → Term -- addition of 2 Terms is a Term
    _-_ : Term → Term → Term -- addition of 2 Terms is a Term
    _*_ : Term → Term → Term -- multiplication of 2 Terms is a Term
    _/_ : Term → Term → Term -- division of 2 Terms is a Term
infixl 6  _+_
infixl 6  _-_
infixl 7  _*_
infixl 7  _/_

_² : Term → Term  -- abbreviation for squaring
a ² = a * a

2×_ : Term → Term -- abbreviation for doubling
2× a = a + a

_⁻¹ : Term → Term
a ⁻¹ = ` one / a

_/2 : Term → Term
a /2 = a * (` two ⁻¹)
_/4 : Term → Term
a /4 = a * (` four ⁻¹)

1/2 = (` one / ` two)

------------------------------NECESSARY RULES---------------------------------------

postulate
    assoc+  : ∀ {a b c : Term}  → (a + b) + c ≡ a + (b + c)
    assoc*  : ∀ {a b c : Term}  → (a * b) * c ≡ a * (b * c)
    comm+   : ∀ {a b : Term}    →       a + b ≡ b + a
    comm*   : ∀ {a b : Term}    →       a * b ≡ b * a
    distr   : ∀ {a b c : Term}  → (a + b) * c ≡ (a * c) + (b * c)

------------------------------PROOF OF BINOMIAL FORMULA-----------------------------

binom : ∀ {a b : Term} → (a + b) ² ≡ (a ² + (2× (a * b) + b ²))

binom {a} {b} =                 begin   (a + b) ²
    ≡⟨ refl ⟩                           (a + b) * (a + b)
    ≡⟨ distr ⟩                          (a * (a + b))   + (b * (a + b))
    ≡⟨ cong (_+ b * (a + b)) 
      comm* ⟩                           ((a + b) * a)   + (b * (a + b))
    ≡⟨ cong (_+ b * (a + b)) 
      distr ⟩                           (a * a + b * a) + (b * (a + b))
    ≡⟨ refl ⟩                           (a ²   + b * a) + (b * (a + b))
    ≡⟨ cong ((a ² + b * a) +_) 
      comm* ⟩                           (a ²   + b * a) + ((a + b) * b)
    ≡⟨ cong ((a ² + b * a) +_) 
      distr ⟩                           (a ²   + b * a) + (a * b + b * b)
    ≡⟨ assoc+ ⟩                         a ² +  (b * a + (a * b + b * b))
    ≡⟨ cong (a ² +_) 
      (sym assoc+) ⟩                    a ² + ((b * a + a * b) + b * b)
    ≡⟨ cong (a ² +_) refl ⟩             a ² + ((b * a + a * b) + b ²)
    ≡⟨ cong (a ² +_)
      (cong (_+ b ²)
      (cong (_+ (a * b)) 
      comm*)) ⟩                         a ² + ((a * b + a * b) + b ²)
    ≡⟨ cong (a ² +_)
      (cong (_+ b ²) refl) ⟩            a ² + (2× (a * b) + b ²)    ∎-qed

------------------------------NECESSARY RULES (2) ----------------------------------

postulate
    2×a     : ∀ {a : Term} → (a + a) ≡ a * ` two            -- need these postulates
    assoc-  : ∀ {a b c : Term} → (a + b) - c ≡ a + (b - c)  -- because the operators 
    a/b     : ∀ {a b : Term} → a / b ≡ a * (b ⁻¹)           -- (+,*,/,-) aren't
    2^2=4   : ` two ² ≡ ` four                              -- defined properly

    inv+    : ∀ {a : Term} → a - a ≡ ` zero
    neutr+  : ∀ {a : Term} → a + ` zero ≡ a
    inv*    : ∀ {a : Term} → a * (a ⁻¹) ≡ ` one
    neutr*  : ∀ {a : Term} → a * ` one  ≡ a


---------------PROOF THAT (x + p /2)² - (p ² /4) + q ≡ x ² + p * x + q -------------


distr^2* : ∀ {a b : Term} → (a * b) ² ≡ (a ² * b ²)
distr^2* {a} {b} = begin    (a * b) ² 
    ≡⟨ refl ⟩               (a * b) * (a * b)
    ≡⟨ assoc* ⟩             a * (b * (a * b))
    ≡⟨ cong (a *_) 
      (sym assoc*) ⟩        a * ((b * a) * b)
    ≡⟨ cong (a *_) 
      (cong (_* b) 
      comm*) ⟩              a * ((a * b) * b)
    ≡⟨ cong (a *_) assoc* ⟩ a * (a * (b * b))
    ≡⟨ sym assoc* ⟩         a * a * (b * b)
    ≡⟨ refl ⟩               a ² * b ²     ∎-qed

inv^2 : ∀ {a : Term} → (a ⁻¹)² ≡ (a ²)⁻¹
inv^2 {a} =     begin               (a ⁻¹)²
    ≡⟨ sym neutr* ⟩                 (a ⁻¹)² * ` one
    ≡⟨ cong ((a ⁻¹)² *_) 
      (sym (inv* {a = (a ²)})) ⟩    (a ⁻¹)² * (a ² * (a ²)⁻¹)
    ≡⟨ sym assoc* ⟩                 ((a ⁻¹)² * a ²) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
       refl ⟩                       ((a ⁻¹ * a ⁻¹) * (a * a)) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
       assoc* ⟩                     (a ⁻¹ * (a ⁻¹ * (a * a))) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
      (cong (a ⁻¹ *_)
      (sym assoc*)) ⟩               (a ⁻¹ * ((a ⁻¹ * a) * a)) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
      (cong (a ⁻¹ *_) 
      (cong (_* a) 
      comm*)) ⟩                     (a ⁻¹ * ((a * a ⁻¹) * a)) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
      (cong (a ⁻¹ *_) 
      (cong (_* a) inv*)) ⟩         (a ⁻¹ * (` one * a)) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
      (cong (a ⁻¹ *_) 
      comm*) ⟩                      (a ⁻¹ * (a * ` one)) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) 
      (cong (a ⁻¹ *_) 
      neutr*) ⟩                     (a ⁻¹ * a) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) comm* ⟩    (a * a ⁻¹) * (a ²)⁻¹
    ≡⟨ cong (_* (a ²)⁻¹) inv* ⟩     ` one * (a ²)⁻¹
    ≡⟨ comm* ⟩                      (a ²)⁻¹ * ` one
    ≡⟨ neutr* ⟩                     (a ²)⁻¹ ∎-qed

distr^2/ : ∀ {a b : Term} → (a / b) ² ≡ (a ² / b ²)
distr^2/ {a} {b} = begin            (a / b) ² 
    ≡⟨ cong _² a/b ⟩                (a * (b ⁻¹))²
    ≡⟨ distr^2* ⟩                   a ² * (b ⁻¹)²
    ≡⟨ cong (a ² *_) inv^2 ⟩        a ² * (b ²)⁻¹
    ≡⟨ sym a/b ⟩                    (a ² / b ²) ∎-qed

2*a/2 : {a : Term} → 2× (a /2) ≡ a
2*a/2 {a} =         begin   2× (a /2) 
    ≡⟨ refl ⟩               a /2 + a /2 
    ≡⟨ 2×a ⟩                (a /2) * ` two
    ≡⟨ refl ⟩               (a * (` two ⁻¹)) * ` two
    ≡⟨ assoc* ⟩             a * ((` two ⁻¹) * ` two) 
    ≡⟨ cong (a *_) 
      comm* ⟩               a * (` two * (` two ⁻¹))  
    ≡⟨ cong (a *_) 
      inv* ⟩                a * ` one 
    ≡⟨ neutr* ⟩             a   ∎-qed

2ab/2 : ∀ {a b : Term} → 2× (a * (b /2)) ≡ a * b
2ab/2 {a} {b} =         begin      (2× (a * (b /2)))
    ≡⟨ refl ⟩                      (2× (a * (b * 1/2))) 
    ≡⟨ cong 2×_ 
      (sym assoc*) ⟩               2× ((a * b) * 1/2) 
    ≡⟨ 2*a/2 ⟩                     (a * b)  ∎-qed

[p/2]² : ∀ {p : Term} → (p /2) ² ≡ (p ² /4)
[p/2]² {p} =    begin           (p /2) ²
    ≡⟨ refl ⟩                   (p * (` two ⁻¹))²
    ≡⟨ distr^2* ⟩               (p ² * (` two ⁻¹)²)
    ≡⟨ cong (p ² *_) inv^2 ⟩    (p ² * (` two ²) ⁻¹)
    ≡⟨ cong (p ² *_) 
      (cong _⁻¹ 2^2=4) ⟩        (p ² * (` four) ⁻¹)
    ≡⟨ refl ⟩                   (p ² /4) ∎-qed

pq : ∀ {x p q : Term} → ((x + p /2)² - (p ² /4))  + q ≡ (x ² + p * x) + q
pq {x} {p} {q} =                begin   ((x + p /2)² - (p ² /4))  + q 
    ≡⟨ cong (_+ q) 
      (cong (_- (p ² /4)) 
      binom) ⟩                          ((x ² + (2× (x * (p /2)) + (p /2) * (p /2))) - (p ² /4))  + q
    ≡⟨ cong (_+ q) 
      assoc- ⟩                          (x ² + ((2× (x * (p /2)) + (p /2) * (p /2)) - (p ² /4)))  + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
      assoc-) ⟩                         (x ² + (2× (x * (p /2)) + ((p /2) * (p /2) - (p ² /4))))  + q
    ≡⟨ refl ⟩                           (x ² + (2× (x * (p /2)) + ((p /2) ² - (p ² /4))))  + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
      (cong (2× (x * (p /2)) +_) 
      (cong (_- (p ² /4)) 
      [p/2]²))) ⟩                       (x ² + (2× (x * (p /2)) + ((p ² /4) - (p ² /4))))  + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
      (cong (2× (x * (p /2)) +_) 
      inv+)) ⟩                          (x ² + (2× (x * (p /2)) + ` zero))  + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
        neutr+) ⟩                       (x ² + (2× (x * (p /2))))  + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
      2ab/2) ⟩                          (x ² + x * p) + q
    ≡⟨ cong (_+ q) 
      (cong (x ² +_) 
      comm*) ⟩                          (x ² + p * x) + q   ∎-qed 
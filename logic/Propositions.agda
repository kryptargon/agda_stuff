module Propositions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.String
open import Relation.Nullary using (¬_) renaming (Dec to Dec'; yes to yes'; no to no')
open import Data.String using (String) renaming (_≟_ to _≟-String'_)

data Form : Set where
    atom : String → Form

    ⟨_∧_⟩ : Form → Form → Form
    ⟨_∨_⟩ : Form → Form → Form
    ⟨_⇒_⟩ : Form → Form → Form
    ⟨_⇔_⟩ : Form → Form → Form

    ¬-_ : Form → Form

data Truth : Set where
    W : Truth
    F : Truth
    undef : Truth

infixl 5 _▷_
data Context (A : Set) : ℕ → Set where
  ∅   : Context A zero
  _▷_ : ∀ {n} → Context A n → A → Context A (suc n)

data _∈_ {A : Set} : A → List A → Set where

  Z : ∀ {xs x}
    → x ∈ (x ∷ xs)

  S_ : ∀ {xs x y}
    → x ∈ xs
      ------------
    → x ∈ (y ∷ xs)

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

_≟-String_ : (x y : String) → Dec (x ≡ y)
x ≟-String y with x ≟-String' y
... | yes' eq = yes eq
... | no'  eq = no  eq

_eval_ : ∀ {n} → Context String n → Form → Truth
∅ eval f = undef
(a ▷ s) eval atom s₁ with s ≟-String s₁
... | yes s=s₁ = {!   !}
... | no s≠s₁ = a eval atom s
(a ▷ x) eval ⟨ f ∧ f₁ ⟩ = {!   !}
(a ▷ x) eval ⟨ f ∨ f₁ ⟩ = {!   !}
(a ▷ x) eval ⟨ f ⇒ f₁ ⟩ = {!   !}
(a ▷ x) eval ⟨ f ⇔ f₁ ⟩ = {!   !}
(a ▷ x) eval (¬- f) = {!   !}

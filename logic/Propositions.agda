module Propositions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _>_)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

data Formula : Set where
  atom : String → Formula

  ⟨_∧_⟩ : Formula → Formula → Formula
  ⟨_∨_⟩ : Formula → Formula → Formula
  ⟨_⇒_⟩ : Formula → Formula → Formula
  ⟨_⇔_⟩ : Formula → Formula → Formula

  ¬-_ : Formula → Formula

litcount : Formula → ℕ
litcount (atom x) = 1
litcount ⟨ a₁ ∧ a₂ ⟩ = litcount a₁ + litcount a₂
litcount ⟨ a₁ ∨ a₂ ⟩ = litcount a₁ + litcount a₂
litcount ⟨ a₁ ⇒ a₂ ⟩ = litcount a₁ + litcount a₂
litcount ⟨ a₁ ⇔ a₂ ⟩ = litcount a₁ + litcount a₂
litcount (¬- a) = litcount a

a+b→0 : ∀ {a b : ℕ}
    → a + b ≡ 0
    → b ≡ 0
a+b→0 {zero} {zero} a+b=0 = refl

litcount>0 : ∀ {f : Formula}
    → (litcount f) ≢ 0
litcount>0 {⟨ f₁ ∧ f₂ ⟩} lf≡0 = litcount>0 {f₂} (a+b→0 lf≡0)
litcount>0 {⟨ f₁ ∨ f₂ ⟩} lf≡0 = litcount>0 {f₂} (a+b→0 lf≡0)
litcount>0 {⟨ f₁ ⇒ f₂ ⟩} lf≡0 = litcount>0 {f₂} (a+b→0 lf≡0)
litcount>0 {⟨ f₁ ⇔ f₂ ⟩} lf≡0 = litcount>0 {f₂} (a+b→0 lf≡0)
litcount>0 {¬- f} lf≡0 = litcount>0 {f} lf≡0

junccount : Formula → ℕ
junccount (atom x) = 0
junccount ⟨ a₁ ∧ a₂ ⟩ = junccount a₁ + junccount a₂ + 1
junccount ⟨ a₁ ∨ a₂ ⟩ = junccount a₁ + junccount a₂ + 1
junccount ⟨ a₁ ⇒ a₂ ⟩ = junccount a₁ + junccount a₂ + 1
junccount ⟨ a₁ ⇔ a₂ ⟩ = junccount a₁ + junccount a₂ + 1
junccount (¬- a) = junccount a

symcount : Formula → ℕ
symcount (atom x) = 1
symcount ⟨ f₁ ∧ f₂ ⟩ = symcount f₁ + symcount f₂ + 3
symcount ⟨ f₁ ∨ f₂ ⟩ = symcount f₁ + symcount f₂ + 3
symcount ⟨ f₁ ⇒ f₂ ⟩ = symcount f₁ + symcount f₂ + 3
symcount ⟨ f₁ ⇔ f₂ ⟩ = symcount f₁ + symcount f₂ + 3
symcount (¬- f) = symcount f + 1

lit→junc : ∀ {f : Formula} {n : ℕ}
  → litcount f ≡ suc n
  → junccount f ≡ n
lit→junc {atom x} refl = refl
lit→junc {⟨ f₁ ∧ f₂ ⟩} lit = {!   !}
lit→junc {⟨ f₁ ∨ f₂ ⟩} lit = {!!}
lit→junc {⟨ f₁ ⇒ f₂ ⟩} lit = {!!}
lit→junc {⟨ f₁ ⇔ f₂ ⟩} lit with litcount f₁ | litcount f₂
lit→junc {⟨ f₁ ⇔ f₂ ⟩} refl | zero | suc l2 with litcount>0 {f₁} {!   !}
... | ()
lit→junc {⟨ f₁ ⇔ f₂ ⟩} refl | suc l1 | zero with litcount>0 {f₂} {!   !}
... | ()
lit→junc {⟨ f₁ ⇔ f₂ ⟩} refl | suc l1 | suc l2 = {!   !}
lit→junc {¬- f} lit = lit→junc {f} lit

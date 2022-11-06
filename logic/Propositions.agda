module Propositions where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.String

data SForm : Set where
  atom : String → SForm

  ⟨_∧_⟩ : SForm → SForm → SForm
  ⟨_∨_⟩ : SForm → SForm → SForm

  ¬-_ : SForm → SForm

infixl 6 ¬-_
infix 5 ⟨_∧_⟩ ⟨_∨_⟩

postulate
    DM-∨ : ∀ {f₁ f₂ : SForm} → ¬- ⟨ f₁ ∨ f₂ ⟩ ≡ ⟨ ¬- f₁ ∧ ¬- f₂ ⟩
    DM-∧ : ∀ {f₁ f₂ : SForm} → ¬- ⟨ f₁ ∧ f₂ ⟩ ≡ ⟨ ¬- f₁ ∨ ¬- f₂ ⟩
    DM-¬¬ : ∀ {f₁ : SForm} → ¬- ¬- f₁ ≡ f₁

replace : SForm → SForm
replace (atom A)    = ¬- atom A
replace ⟨ f₁ ∧ f₂ ⟩ = ⟨ replace f₁ ∨ replace f₂ ⟩
replace ⟨ f₁ ∨ f₂ ⟩ = ⟨ replace f₁ ∧ replace f₂ ⟩
replace (¬- f)      = ¬- replace f

--------------------------PROOF THAT f* ≡ ¬ f-----------------------

replace≅¬ : ∀ (f : SForm) → replace f ≡ ¬- f

replace≅¬ (atom A) = refl

replace≅¬ ⟨ f₁ ∧ f₂ ⟩ with replace≅¬ f₁ | replace≅¬ f₂
... | f₁*≡¬f₁ | f₂*≡¬f₂ =       
        begin                           ⟨ replace f₁ ∨ replace f₂ ⟩ 
    ≡⟨ cong ⟨_∨ replace f₂ ⟩ f₁*≡¬f₁ ⟩  ⟨ ¬- f₁ ∨ replace f₂ ⟩
    ≡⟨ cong ⟨ ¬- f₁ ∨_⟩ f₂*≡¬f₂ ⟩       ⟨ ¬- f₁ ∨ ¬- f₂ ⟩
    ≡⟨ sym DM-∧ ⟩                       ¬- ⟨ f₁ ∧ f₂ ⟩ 
    ∎

replace≅¬ ⟨ f₁ ∨ f₂ ⟩ with replace≅¬ f₁ | replace≅¬ f₂ 
... | f₁*≡¬f₁ | f₂*≡¬f₂ = 
        begin                           ⟨ replace f₁ ∧ replace f₂ ⟩ 
    ≡⟨ cong ⟨_∧ replace f₂ ⟩ f₁*≡¬f₁ ⟩  ⟨ ¬- f₁ ∧ replace f₂ ⟩ 
    ≡⟨ cong ⟨ ¬- f₁ ∧_⟩ f₂*≡¬f₂ ⟩       ⟨ ¬- f₁ ∧ ¬- f₂ ⟩
    ≡⟨ sym DM-∨ ⟩                       ¬- ⟨ f₁ ∨ f₂ ⟩ 
    ∎

replace≅¬ (¬- f) with replace≅¬ f
... | f*≡¬f =               
        begin                       (¬- replace f)
            ≡⟨ cong ¬-_ f*≡¬f ⟩     ¬- (¬- f) 
            ∎
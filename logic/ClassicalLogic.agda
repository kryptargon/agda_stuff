-- From plfa https://plfa.github.io/Negation/ (negation, with intuitionistic and classical logic)

-- Product type (Conjunction)
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ :
      A
    → B
      -----
    → A × B
infixr 2 _×_

proj₁ : ∀ {A B : Set}
  → A × B
    -----
  → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : ∀ {A B : Set}
  → A × B
    -----
  → B
proj₂ ⟨ x , y ⟩ = y


--- Sum type (Disjunction)
data _⊎_ (A B : Set) : Set where
  inj₁ :
      A
      -----
    → A ⊎ B

  inj₂ :
      B
      -----
    → A ⊎ B
infixr 1 _⊎_

-- Empty type (falsum)
data ⊥ : Set where
    --

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

-- Lemmas
⊥-elim : ∀ {A : Set}
  → ⊥
    --
  → A
⊥-elim ()


⊎-comm : ∀ {A B : Set}
  → A ⊎ B
  ----------
  → B ⊎ A
⊎-comm (inj₁ x) = inj₂ x
⊎-comm (inj₂ y) = inj₁ y

→-trans : ∀ {A B C : Set}
    → (A → B)
    → (B → C)
    ----------
    → (A → C)
→-trans A→B B→C A = B→C (A→B A)

-- the following rules of classical logic imply each other
ExMiddle : Set₁
¬¬-elim  : Set₁
Peirce's : Set₁
Imp-Disj : Set₁
DeMorgan : Set₁

ExMiddle = (∀ {A : Set} → (A ⊎ ¬ A))
¬¬-elim  = (∀ {A : Set} → (¬ ¬ A → A))
Peirce's = (∀ {A B : Set} → ((A → B) → A) → A)
Imp-Disj = (∀ {A B : Set} → (A → B) → (¬ A ⊎ B))
DeMorgan = (∀ {A B : Set} → (¬ (¬ A × ¬ B) → A ⊎ B))

-- Proofs:
1→2 : ExMiddle → ¬¬-elim
1→2 A⊎¬A ¬¬Z with A⊎¬A 
...             | inj₁ A = A
...             | inj₂ ¬A = ⊥-elim (¬¬Z ¬A)

2→3 : ¬¬-elim → Peirce's
2→3 ¬¬A→A = λ [Y→Z]→Y → ¬¬A→A (λ ¬Y → ¬Y ([Y→Z]→Y (λ Y → ¬¬A→A (λ ¬Z → ¬Y Y))))

3→4 : Peirce's → Imp-Disj
3→4 [[A→B]→A]→A = λ Y→Z → [[A→B]→A]→A (λ [¬Y→Z] → inj₁ λ Y → [¬Y→Z] (inj₂ (Y→Z Y)))

4→5 : Imp-Disj → DeMorgan
4→5 impdis ¬[¬Y×¬Z] = 1→2 (Imp-Disj→em impdis) λ ¬[A⊎B] 
         → ¬[¬Y×¬Z] ⟨ (λ A → ¬[A⊎B] (inj₁ A)) , (λ B → ¬[A⊎B] (inj₂ B)) ⟩
  where
  Imp-Disj→em : ∀ {A : Set}
    → Imp-Disj
    -----------
    → A ⊎ ¬ A
  Imp-Disj→em impdis = ⊎-comm (impdis (λ z → z))

5→1 : DeMorgan → ExMiddle
5→1 X = X (λ z → proj₂ z (proj₁ z))
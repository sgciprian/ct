import .category

namespace category_theory

-- Given a category C:
-- Object A ∈ C₀ is initial if there is a unique morphism from A to every object B ∈ C₀
def isInitial (C : category) (A : C.C₀) : Prop :=
  ∀ (B : C.C₀) (f g : C.hom A B), f = g

structure initialObject (C : category) (A : C.C₀) :=
  (property : isInitial C A)


-- Given a category C:
-- Object B ∈ C₀ is terminal if there is a unique morphism from every object A ∈ C₀ to B
def isTerminal (C : category) (B : C.C₀) : Prop :=
  ∀ (A : C.C₀) (f g : C.hom A B), f = g

structure terminalObject (C : category) (B : C.C₀) :=
  (property : isTerminal C B)


-- Given category C and objects A, B ∈ C₀:
-- A triple (P, π₁: P ⟶ A, π₂: P ⟶ B) is called a product of A and B if
-- for any triple (Q, q₁: Q ⟶ A, q₂: Q ⟶ B) there is a unique morphism f: Q ⟶ P
-- such that π₁ ∘ f = q₁ and π₂ ∘ f = q₂
def isBinaryProduct (C : category) {A B : C.C₀} (P : C.C₀) (π₁ : C.hom P A) (π₂ : C.hom P B) : Prop :=
                        ∀ (Q : C.C₀) (q₁ : C.hom Q A) (q₂ : C.hom Q B),
                          ∃! (f : C.hom Q P), C.compose π₁ f = q₁ ∧ C.compose π₂ f = q₂

structure binaryProduct (C : category) (A B : C.C₀) :=
  (P : C.C₀)
  (π₁ : C.hom P A)
  (π₂ : C.hom P B)
  (property : isBinaryProduct C P π₁ π₂)


-- Given category C and objects A, B ∈ C₀:
-- A triple (Cₚ, ι₁: A ⟶ Cₚ, ι₂: B ⟶ Cₚ) is called a coproduct of A and B if
-- for any triple (D, i₁: A ⟶ D, i₂: B ⟶ D) there is a unique morphism f: Cₚ ⟶ D
-- such that f ∘ ι₁ = i₁ and f ∘ ι₂ = i₂
def isBinaryCoproduct (C : category) {A B : C.C₀} (Cₚ : C.C₀) (ι₁ : C.hom A Cₚ) (ι₂ : C.hom B Cₚ) : Prop :=
                        ∀ (D : C.C₀) (i₁ : C.hom A D) (i₂ : C.hom B D),
                          ∃! (f : C.hom Cₚ D), C.compose f ι₁ = i₁ ∧ C.compose f ι₂ = i₂
 
structure binaryCoproduct (C : category) (A B : C.C₀) :=
  (Cₚ : C.C₀)
  (ι₁ : C.hom A Cₚ)
  (ι₂ : C.hom B Cₚ)
  (property : isBinaryCoproduct C Cₚ ι₁ ι₂)

end category_theory
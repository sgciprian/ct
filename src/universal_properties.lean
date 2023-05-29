import .category

namespace category_theory

def isInitial (C : category) (A : C.C₀) : Prop :=
  ∀ (B : C.C₀) (f g : C.hom A B), f = g

structure initialObject (C : category) (A : C.C₀) :=
  (property : isInitial C A)

def isTerminal (C : category) (B : C.C₀) : Prop :=
  ∀ (A : C.C₀) (f g : C.hom A B), f = g

structure terminalObject (C : category) (B : C.C₀) :=
  (property : isTerminal C B)


def isBinaryProduct (C : category) {A B : C.C₀} (P : C.C₀) (π₁ : C.hom P A) (π₂ : C.hom P B) : Prop :=
                        ∀ (Q : C.C₀) (q₁ : C.hom Q A) (q₂ : C.hom Q B),
                          ∃! (f : C.hom Q P), C.compose π₁ f = q₁ ∧ C.compose π₂ f = q₂

structure binaryProduct (C : category) (A B : C.C₀) :=
  -- product of A and B
  (P : C.C₀)
  (π₁ : C.hom P A)
  (π₂ : C.hom P B)

  (universal_property : isBinaryProduct C P π₁ π₂)
  
structure binaryCoproduct (C : category) (A B : C.C₀) :=
  -- coproduct of A and B
  (Cp : C.C₀)
  (l₁ : C.hom A Cp)
  (l₂ : C.hom B Cp)

  -- map
  (f : ∀ {D : C.C₀}, C.hom Cp D)
  
  -- axioms
  (commutes_left : ∀ {D : C.C₀} (i₁ : C.hom A D), C.compose f l₁ = i₁)
  (commutes_right : ∀ {D : C.C₀} (i₂ : C.hom B D), C.compose f l₂ = i₂)
  (uniqueness : ∀ {D : C.C₀} (i₁ : C.hom A D) (i₂ : C.hom B D) (g : C.hom Cp D), C.compose g l₁ = i₁ → C.compose g l₂ = i₂ → g = f)
  
end category_theory
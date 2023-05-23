import .category

namespace category_theory

structure monomorphism [C : category] {X Y Z : C.C₀} (f : C.hom X Y) :=
  (mono : ∀ {g₁ g₂ : C.hom Z X}, C.compose f g₁ = C.compose f g₂ → g₁ = g₂)

structure epimorphism [C : category] {X Y Z : C.C₀} (f : C.hom X Y) :=
  (epi : ∀ {g₁ g₂ : C.hom Y Z}, C.compose g₁ f = C.compose g₂ f → g₁ = g₂)

structure isomorphism [C : category] {X Y : C.C₀} (f : C.hom X Y) :=
  (iso : ∃ (g : C.hom Y X),((C.compose g f) = (C.id X)) ∧ ((C.compose f g) = (C.id Y)))

structure sectionRetractionPair [C : category] {X Y : C.C₀} (s : C.hom X Y) (r : C.hom Y X) :=
  (r_s : C.compose r s = C.id X)

end category_theory

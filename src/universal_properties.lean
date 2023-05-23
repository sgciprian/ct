import .category

namespace category_theory

def is_initial [C : category] (X : C.C₀) : Prop :=
  ∀ (Y : C.C₀), ∃ (f g : C.hom X Y), f = g

structure initiality [C : category] (X : C.C₀) :=
  (initial : ∀ (Y : C.C₀), ∃ (f g : C.hom X Y), f = g)

def is_terminal [C : category] (Y : C.C₀) : Prop :=
  ∀ (X : C.C₀), ∃ (f g : C.hom X Y), f = g

structure terminality [C : category] (Y : C.C₀) :=
  (terminal : ∀ (X : C.C₀), ∃ (f g : C.hom X Y), f = g)

end category_theory
universes u v

namespace category_theory

-- set_option pp.all true
structure category :=
  --attributes
  (C₀     : Sort u)
  (hom     : Π (X Y : C₀), Sort v)
  (id      : Π (X : C₀), hom X X)
  (compose : Π {X Y Z : C₀} (g : hom Y Z) (f : hom X Y), hom X Z)
  --axioms
  (left_id  : ∀ {X Y : C₀} (f : hom X Y), compose f (id X) = f)
  (right_id : ∀ {X Y : C₀} (f : hom X Y), compose (id Y) f = f)
  (assoc    : ∀ {X Y Z W : C₀} (f : hom X Y) (g : hom Y Z) (h : hom Z W), compose h (compose g f) = compose (compose h g) f)

--notation
infixr `⟶`:90 := category.hom
infix (name := category_compose) `∘`:90 := category.compose
notation `𝟙` := category.id

end category_theory
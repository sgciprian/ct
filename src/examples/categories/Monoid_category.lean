-- A monoid can be represented as a category with one object.
import category

-- Since every instance of true is considered to be the same it can be used as our bare type.
instance monoid : category :=
{
  obj      := true,
  hom      := λ x y, nat, -- here I implemented the monoid of ℕ with the + operation.
  id       := λ x, 0,
  compose  := λ _ _ _ f g, f + g, 
  left_id  := begin intros, apply nat.add_zero end,
  right_id := begin intros, apply nat.zero_add end,
  assoc    := begin intros, symmetry, apply nat.add_assoc end
}

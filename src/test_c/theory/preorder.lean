-- i know mathlib includes a preorder type class,
-- but that has more properties than in CT4P
namespace ct

universe u

class preorder (α : Type u) extends has_le α :=
(refl  : ∀ (x : α), x ≤ x)
(trans : ∀ (x y z : α), (x ≤ y ∧ y ≤ z) → x ≤ z)
-- done with preorder

end ct
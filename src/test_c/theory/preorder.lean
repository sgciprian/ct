-- i know mathlib includes a preorder type class,
-- but that has more properties than in CT4P
namespace ct

class preorder :=
(memb  : Type*)
(le    : memb → memb → Prop)
-- TODO don't know how to parametrize this maybe?
(infix (name := preorder_le ) `≤`:50 := le)
(refl  : ∀ (x : memb), x ≤ x)
(trans : ∀ (x y z : memb), (x ≤ y ∧ y ≤ z) → x ≤ z)
-- done with preorder

end ct
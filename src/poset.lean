import .preorder

namespace category_theory

universe u

class poset (α : Type u) extends preorder α :=
(antisymm  : ∀ (x y : α), x ≤ y ∧ y ≤ x → x = y)
-- done with poset

-- This is a structure bundling a type (set) and its instance
-- for poset (proof that it is a poset) together.
structure poset_u :=
(memb  : Type*)
(proof : poset memb)

-- This allows us to write x : X when X : poset_u by converting
-- converting the term X to the underlying type memb.
instance coe_poset_uni : has_coe_to_sort poset_u Type* :=
{
  coe := λ p, p.memb
}

-- This uses the fact that `poset memb` implies that the memb type
-- has a ≤ operator to give ≤ to terms of type X.
instance poset_uni_has_le (X : poset_u) : has_le X :=
{
  le := X.proof.le
}

end category_theory
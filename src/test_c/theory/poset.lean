import test_c.theory.preorder
namespace ct

universe u

class poset (α : Type u) extends preorder α :=
(antisymm  : ∀ (x y : α), x ≤ y ∧ y ≤ x → x = y)
-- done with class

end ct
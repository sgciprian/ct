import test_c.theory.preorder
namespace ct

class poset extends preorder :=
(infix (name := poset_le ) `≤`:50 := le)
(antisymm  : ∀ (x y : memb), x ≤ y ∧ y ≤ x → x = y)
-- done with poset

end ct
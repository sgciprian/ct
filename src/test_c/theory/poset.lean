import test_c.theory.preorder
namespace ct

class poset extends preorder :=
(infix (name := poset_le ) `≤`:50 := le)
(antisymm  : ∀ (x y : memb), x ≤ y ∧ y ≤ x → x = y)
-- done with poset

instance coe_poset : has_coe_to_sort poset Type* :=
{
  coe := λ p, p.memb
}

end ct
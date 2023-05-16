import test_c.theory.poset
namespace ct

class poset_universe :=
(memb  : Type*)
(proof : poset memb)
-- done with poset_universe

instance coe_poset_uni : has_coe_to_sort poset_universe Type* :=
{
  coe := λ p, p.memb
}

instance poset_uni_has_le (X : poset_universe) : has_le poset_universe.memb :=
{
  le := X.proof.le
}

end ct
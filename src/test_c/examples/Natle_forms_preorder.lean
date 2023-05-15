import test_c.theory.category
import test_c.theory.preorder
import test_c.examples.PreXle_category
open ct

-- show that naturals and ≤
-- form a preorded set
-- first show that for naturals ≤ is a preorder
instance nat_leq_is_preorder : preorder :=
{
  memb := ℕ,
  le := λ x y, x ≤ y,
  refl :=
    begin
      intro x,
      apply nat.le_refl,
    end,
  trans :=
    begin
      intros x y z,
      intro h,
      cases h with f g,
      apply nat.le_trans f g,
    end,
}
-- then this typechecks so all good.
def nat_is_pre := Pre nat_leq_is_preorder
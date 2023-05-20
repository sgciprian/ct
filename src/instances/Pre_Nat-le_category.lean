import preorder
import instances.Pre_X_le_category

open category_theory

-- show that naturals and ≤
-- form a preorded set
-- first show that for naturals ≤ is a preorder
instance nat_leq_is_preorder : category_theory.preorder ℕ :=
{
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
def nat_is_pre := Pre ℕ nat_leq_is_preorder

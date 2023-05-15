import test_c.theory.category
import test_c.theory.preorder
open ct

-- Pre
-- category induced by a preordered set X - (memb, le)
instance Pre (X : ct.preorder) : category :=
{
  obj := X.memb,
  hom := X.le,
  id  := λ (x : X.memb),
    begin
      apply preorder.refl,
    end,
  compose := λ {x y z} (g : X.le y z) (f : X.le x y),
    begin
      apply preorder.trans x y z,
      split,
      exact f,
      exact g,
    end,
  left_id :=
    begin
      intros,
      simp,
    end,
  right_id :=
    begin
      intros,
      simp,
    end,
  assoc :=
    begin
      intros,
      simp,
    end,
}

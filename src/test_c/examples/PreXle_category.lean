import test_c.theory.category
import test_c.theory.preorder
open ct

-- Pre(X, ≤)
-- category induced by a preordered set (X, ≤)
-- → but as above, X can be represented as a type
-- → proof is the instance of the preorder type class
instance Pre (X : Type*) (proof : ct.preorder X) : category :=
{
  obj := X,
  hom := λ (x y : X), x ≤ y,
  id  := λ (x : X),
    begin
      apply proof.refl,
    end,
  compose := λ {x y z} (g : y ≤ z) (f : x ≤ y),
    begin
      apply proof.trans x y z,
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

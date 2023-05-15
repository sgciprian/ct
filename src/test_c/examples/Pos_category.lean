import test_c.theory.category
import test_c.theory.poset
open ct

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := Σ α, ct.preorder α,
  hom := λ X Y, X.1 ≤ Y.1,
  id  := λ X, ct.poset_id X.2,
  compose :=
    begin
      intros,

    end,
}

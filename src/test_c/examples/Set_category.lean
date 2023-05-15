import test_c.theory.category
open ct

-- set α is the type of subsets of type α in Lean,
-- so basically a set is a Lean type

-- Set
-- category of sets
instance Set : category :=
{
  obj := Type*,
  hom := λ X Y, X → Y,
  id  := λ X, λ (x : X), x,
  compose := λ {X Y Z} (g : Y → Z) (f : X → Y), g ∘ f,
  -- these proofs can all be just {intros, simp}
  -- but i think it's more readable this way
  left_id :=
    begin
      intros,
      apply function.comp.right_id,
    end,
  right_id :=
    begin
      intros,
      apply function.comp.left_id,
    end,
  assoc :=
    begin
      intros,
      apply function.comp.assoc,
    end,
}
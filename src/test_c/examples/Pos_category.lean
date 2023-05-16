import test_c.theory.category
import test_c.theory.poset_universe
import data.subtype
open ct

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := poset_universe,
  hom := λ X Y, {f : X → Y // ∀ (x y : X), x ≤ y → (f x) ≤ (f y)},
  id  := λ X, ⟨id, begin
      intros x y h₁,
      simp,
      exact h₁,
    end⟩,
  compose := λ X Y Z g f, ⟨g.val ∘ f.val,
    begin
      intros x y h₁,
      simp,
      have fp := f.property,
      have gp := g.property,
      apply gp,
      apply fp,
      exact h₁,
    end⟩,
  left_id :=
    begin
      simp,
    end,
  right_id :=
    begin
      simp,
    end,
  assoc :=
    begin
      intros,
      simp,
    end,
}

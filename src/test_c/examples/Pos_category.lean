import test_c.theory.category
import test_c.theory.poset
import data.subtype
open ct

def pos_hom (X Y : poset):= {f : X.memb → Y.memb // ∀ x₁ x₂ : X.memb, X.le x₁ x₂ → Y.le (f x₁) (f x₂)}

--def pos_uniq_hom : ∀ (X Y : poset), 

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := Σ α, poset α,
  hom := λ X Y, {f : X.1 → Y.1 // ∀ (x y : X.1), X.2.le x y → Y.2.le (f x) (f y)},
  id  := λ X, ⟨id, begin
      intros x y h₁,
      simp,
      exact h₁,
    end⟩,
  compose := λ X Y Z g f, ⟨g.1 ∘ f.1,
    begin
      intros x y h₁,
      simp,
      have fp := f.property,
      have gp := g.property,
      apply gp (f.val x) (f.val y),
      apply fp x y,
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

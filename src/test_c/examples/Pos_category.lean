import test_c.theory.category
import test_c.theory.poset
import data.subtype
open ct

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := poset,
  hom := λ X Y, {f : X.memb → Y.memb // ∀ x₁ x₂, X.le x₁ x₂ → Y.le (f x₁) (f x₂)},
  id  := λ X, ⟨id, begin
      intros x₁ x₂ h,
      exact h,
    end⟩,
  compose := λ {X Y Z} g f, ⟨g.val ∘ f.val, 
    begin
      intros x₁ x₂ h,
      cases f with ff fp,
      cases g with gf gp,
    end⟩,
}

import test_c.theory.category
import test_c.theory.poset
open ct

def pos_hom (X Y : poset):= {f : X.memb → Y.memb // ∀ x₁ x₂ : X.memb, X.le x₁ x₂ → Y.le (f x₁) (f x₂)}

--def pos_uniq_hom : ∀ (X Y : poset), 

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := poset,
  hom := λ X Y, pos_hom X Y,
  id  := λ X, ⟨λx, x, begin
    intros x₁ x₂ h,
    exact h,
  end⟩,
  compose := λ {X Y Z} g f, ⟨λx, g.1 (f.1 x), 
  begin
    intros x₁ x₂ h,
    cases f with ff fp,
    cases g with gf gp,
    sorry,
  end⟩,
  left_id :=
    begin
      intros,
      simp,
    end,
}

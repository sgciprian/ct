import test_c.theory.category
import test_c.theory.poset
open ct

-- Pos
-- category of posets
instance Pos : category :=
{
  obj := Σ α, poset α,
  hom := λ X Y, Σ (f : X.1 → Y.1), ct.poset_morph X.2 Y.2 f,
  id  := λ X, ⟨id, ct.poset_id X.2⟩,
  compose := λ {X Y Z} g f, ⟨g.1 ∘ f.1, ct.poset_compose g.2 f.2⟩,
  left_id :=
    begin
      intros,
      
    end,
}

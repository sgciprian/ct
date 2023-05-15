import test_c.theory.category
open ct

universe u

-- i have no idea what this would represent
-- but i didn't want to delete it xd
instance clueless : category :=
{
  obj := set (Sort u),
  hom := λ (A B : set (Sort u)), ∃ (f : Sort u → Sort u), ∀ (x ∈ A), (f x) ∈ B,
  id  := λ (A : set (Sort u)),
    begin
      apply exists.intro id,
      intro x,
      intro p,
      rw id,
      exact p,
    end,
  compose := λ {X Y Z : set (Sort u)},
    begin
      intros g f,
      cases f with f hf,
      cases g with g hg,
      apply exists.intro (g ∘ f),
      intros x p,
      apply hg,
      apply hf,
      exact p,
    end,
  left_id := λ {X Y : set (Sort u)},
    begin
      intro f,
      cases f with f hf,
      refl,
    end,
  right_id := λ {X Y : set (Sort u)},
    begin
      intro f,
      cases f with f hf,
      refl,
    end,
  assoc := λ {X Y Z W : set (Sort u)},
    begin
      intros f g h,
      cases f with f hf,
      cases g with g hg,
      cases h with h hh,
      refl,
    end
}
import test_c.category
import test_c.preorder
open ct

universe u

-- set α is the type of subsets of type α in Lean,
-- so basically a set is a Lean type

-- Set
-- category of sets
instance Set : category :=
{
  obj := Type,
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

-- Pre(X, ≤)
-- category induced by a preordered set (X, ≤)
-- → but as above, X can be represented as a type
-- → proof is the instance of the preorder type class
instance Pre (X : Type) (proof : ct.preorder X) : category :=
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

-- show that naturals and ≤
-- form a preorded set
-- first show that for naturals ≤ is a preorder
instance nat_leq_is_preorder : ct.preorder ℕ :=
{
  refl :=
    begin
      intro x,
      apply nat.le_refl,
    end,
  trans :=
    begin
      intros x y z,
      intro h,
      cases h with f g,
      apply nat.le_trans f g,
    end,
}
-- then this typechecks so all good.
def nat_is_pre := Pre ℕ nat_leq_is_preorder

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
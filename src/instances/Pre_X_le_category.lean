import category
import preorder

open category_theory

-- Same category but with the old category definition
-- instance nat_le_category : category :=
-- {
--   obj := nat,
--   hom := λ n m, n ≤ m,
--   id := λ n, le_refl n,
--   compose := λ _ _ _ f g, le_trans f g,
--   left_id := λ n m f, begin
--     refl
--   end,
--   right_id := λ n m f, begin
--     refl
--   end,
--   assoc := λ n m p q f g h, begin
--     refl
--   end,
-- }

-- Pre(X, ≤)
-- category induced by a preordered set (X, ≤)
-- → proof is the instance of the preorder type class for X
def Pre (X : Type) (proof : category_theory.preorder X) : category :=
{
  -- as for Set, X can be represented as a type.
  C₀ := X,

  -- x ≤ y is a Prop, this means there is a morphism between x and y
  -- iff x ≤ y is inhabited, so if we can provide a proof that x ≤ y.
  -- Since it's a Prop, we also have that all proofs are essentially
  -- identical; so there may only be at most one morph in hom_c(x, y).
  hom := λ (x y : X), x ≤ y,

  -- In order to show there is an identity for every element x, we
  -- have to prove x ≤ x, which follows instantly from the proof of
  -- preorder.
  id  := λ (x : X),
    begin
      apply proof.refl,
    end,

  -- Composition is same as proving transity, follows from preorder.
  compose := λ {x y z} (g : y ≤ z) (f : x ≤ y),
    begin
      apply proof.trans x y z,
      split,
      exact f,
      exact g,
    end,

  -- Morphisms are props; all proofs are equivalent. So if we already
  -- have a proof f, then it must be equivalent to any other proof.
  left_id :=
    begin
      intros x y f,
      refl,
    end,

  right_id :=
    begin
      intros x y f,
      simp,
    end,
    
  assoc :=
    begin
      intros x y z w f g h,
      simp,
    end,
}

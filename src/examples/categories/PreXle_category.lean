import category
import test_c.theory.preorder
open ct


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
-- → but as above, X can be represented as a type
-- → proof is the instance of the preorder type class
instance Pre (X : Type*) (proof : ct.preorder X) : category :=
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

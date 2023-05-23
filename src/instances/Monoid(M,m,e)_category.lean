import monoid
import category

open category_theory

-- The category Monoid(M,m,e)
-- C₀ is a singleton set
-- M is the hom-set of the category
-- m is the composition in the category
-- e is the identity morphism
def MonoidCategory [b : Type*] [subsingleton b] [C : category] (M : monoid C) : category :=
  {
    C₀ := b,
    hom := λ _ _, C.C₀,
    compose := λ _ _ _ f g, M.m f g,
    id := λ _, M.e,
    left_id :=
    begin
      intros _ _ f,
      exact M.left_id f
    end,
    right_id := 
    begin
      intros _ _ f,
      exact M.right_id f
    end,
    assoc := 
    begin
      intros X Y Z W f g h,
      exact M.assoc h g f
    end
  }

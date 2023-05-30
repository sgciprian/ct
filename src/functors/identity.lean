import functors.functor
namespace category_theory

-- Creates the identity functor of a category.
-- This maps each object and morphism to itself.
def Id (C : category) : functor C C :=
{
  map_obj := λ X : C, X,
  map_hom := λ X Y : C, λ f, f,
  id :=
    begin
      intro X,
      refl,
    end,
  comp :=
    begin
      intros,
      refl,
    end,
}

end category_theory

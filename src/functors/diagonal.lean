import functors.functor
import instances.Product_category

namespace category_theory

-- Δ : C → C × C, Δ(x) = (x, x), ∀ x ∈ 𝒞₀ ∪ Hom𝒞.
def diagonal_functor (C : category) : functor C (Product C C) :=
{
  map_obj := λ (c : C), (c, c),
  map_hom := λ {c d : C} (h : C.hom c d), (h, h),
  id :=
    begin
      intros,
      refl,
    end,
  comp :=
    begin
      intros,
      refl,
    end,
}
-- notation
infixr `Δ`:90 := diagonal_functor

end category_theory
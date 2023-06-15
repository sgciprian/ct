import functors.functor
import universal_properties.binary_product
import universal_properties.product_morphism

namespace category_theory

-- This file contains the definition for a useful but basic
-- functor, the right product functor.
-- Check out Pierce, example 64 (2.10, pg. 29).
--
-- For a category C with binary products and a given object
-- c in C, we can define the functor ─×c mapping objects b
-- to the product object b×c and morphisms  f:b→d to the
-- product of morphisms f×id_c (from b×c to d×c).
def r_product_functor {C : category} [has_all_products C] (c : C) : functor C C :=
{
  -- b → b×c
  map_obj := λ (b : C), (po b c).p,
  -- f → f×id
  map_hom := λ {b d : C} (f : C.hom b d), product_morphism f (C.id c),
  -- already proved (id c)×(id d) = id (c×d)
  id :=
    begin
      intro,
      rw identity_morphism_of_product,
    end,
  -- already proved (g∘f)×(g'∘f') = g×g' ∘ f×f', just need to do some
  -- rewriting so lean lets us apply the lemma
  comp :=
    begin
      intros,
      repeat { rw refl_product_morphism_pm },
      rw product_of_composible_morphisms,
      rw C.left_id,
    end,
}

end category_theory
import functors.functor

namespace category_theory

-- There is already a definition for binary product in the root folder,
-- but it uses ∃ which leads to classical reasoning to get the actual object
-- out of exists.

-- Defines an object in C that has morphisms to two other (specific) objects.
structure binary_product_bundle {C : category} (c d : C) :=
(x : C)
(x₁ : C.hom x c)
(x₂ : C.hom x d)

-- Defines the binary product and its properties for two (specific) objects in C.
structure binary_product {C : category} (c d : C) :=
-- product p is made up of the actual object and its two morphisms
(p : C)
(p₁ : C.hom p c)
(p₂ : C.hom p d)
-- for all other objects x with morphisms to same objects, there is a unique morphism
-- mapping it to p that makes the two triangles in the diagram commute:
--             x
--          ↙  ↓  ↘ 
--        c  ← p →  d 
-- Existence
(ue : Π (x : binary_product_bundle c d), C.hom x.x p)
(ump : ∀ (x : binary_product_bundle c d), x.x₁ = C.compose p₁ (ue x) ∧ x.x₂ = C.compose p₂ (ue x))
-- Uniqueness
(uu : ∀ (x : binary_product_bundle c d) (h : C.hom x.x p), x.x₁ = C.compose p₁ h ∧ x.x₂ = C.compose p₂ h → h = ue x)

def bundle {C : category} {c d : C} (p : binary_product c d) : binary_product_bundle c d :=
{
  x := p.p,
  x₁ := p.p₁,
  x₂ := p.p₂,
}

-- Category with binary products for all pairs of objects.
class has_all_products (C : category) :=
(product : Π (c d : C), binary_product c d)

-- Short-hand for the c×d.
def po {C : category} [has_all_products C] (c d : C) := has_all_products.product c d

end category_theory
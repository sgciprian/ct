import functors.functor
import universal_properties_alt.binary_product
import universal_properties_alt.product_morphism

namespace category_theory

-- Defines the exponent object and its properties for two (specific) objects in C.
structure exponent {C : category} [has_all_products C] (b a : C) :=
-- has object b^a and arrow eval : (b^a × a) → b with universal property 
(ob : C)
(ev : C.hom (po ob a).p b)
-- for all other objects c with morphisms g from c×a to b, there is a unique morphism
-- g⋆ mapping c to b^a×a that makes the triangle in the diagram commute:
--           ev_b^a
--     b^a×a    →      b
--        ↑  
--  g⋆×idₐ|         ↗
--        |       ↗ g
--       c×a
-- Existence
(ue : Π (c : C) (g : C.hom (po c a).p b), C.hom c ob)
(ump : ∀ (c : C) (g : C.hom (po c a).p b), g = C.compose ev (product_morphism (ue c g) (C.id a)))
-- Uniqueness
(uu : ∀ (c : C) (g : C.hom (po c a).p b) (h : C.hom c ob), g = C.compose ev (product_morphism h (C.id a)) → h = ue c g)

-- Category with exponentiation.
class has_exponentiation (C : category) [has_all_products C] :=
(exp : Π (a b : C), exponent a b)

-- Short-hand for b^a.
def exp {C : category} [has_all_products C] [has_exponentiation C] (b a : C) := has_exponentiation.exp b a

-- Pierce example 71 (2.11, pg. 32)
-- Converts morphisms f:b → c to the unique morphism f*:b^a→c^a given by f∘ev_b^a : b^a×a → c.
--               ev_c^a
--      c^a × a    →     c  
--          ↑         ↗
-- unique   |       ↗  f ∘ ev_b^a
--          |     ↗
--      b^a × a
def exp_hom {C : category} [has_all_products C] [has_exponentiation C] (a : C) {b c : C} (f : C.hom b c)
: C.hom (exp b a).ob (exp c a).ob := (exp c a).ue (exp b a).ob (C.compose f (exp b a).ev) 

-- Some useful lemmas.

-- eval with exp_hom acts as some sort of natural transformation (this diagram commutes:)
--                    ev_b^a
--            b^a × a   →      b
--
-- exp_hom × Id_a ↓            ↓ f
-- a f 
--            c^a × a   →      c
--                    ev_c^a
--
-- So it does not matter whether we eval the exponential and then apply f, or apply exp_hom f
-- and the eval the exponential.
lemma simp_exp_hom {C : category} [has_all_products C] [has_exponentiation C] (a : C) {b c : C}
(f : C.hom b c) : C.compose (exp c a).ev (product_morphism (exp_hom a f) (C.id a)) = C.compose f (exp b a).ev :=
  begin
    unfold exp_hom,
    symmetry,
    -- this is exactly the mapping property
    exact (exp c a).ump (exp b a).ob (C.compose f (exp b a).ev),
  end

end category_theory
import .category
import .functors
import .natural_transformation
import .adjunction_hom

namespace category_theory

-- Definition 2.3 https://ncatlab.org/nlab/show/adjoint+functor
-- in terms of unit η / counit ε (Mac Lane pg. 83, Theorem 2 (v))

-- 𝒞 and 𝒟 are two categories with L : 𝒞 → 𝒟 and R : 𝒟 → 𝒞 functors.
-- Then L and R are a pair of adjoint functors (L left adjoint, R right adjoint)
-- L ⊢ R, if we have natural transformations η, ε that fulfill the triangle identities
-- and are defined as such:
--          η : Id D → R ⬝ L
--          ε : L ⬝ R → Id C
--
-- The unit η lets us replace any Id D with R ⬝ L,
-- while the counit ε lets us replace any L ⬝ R with Id C.
--
-- For this to make sense, we need these conditions to be fulfilled:
--
-- identity of C:
-- for any c ∈ C₀, L (η c) maps L c to L (R (L c)),
--             and ε (L c) maps L (R (L c)) to L c.
--
-- identity of D:
-- for any d ∈ D₀, η (R d) maps R d to R (L (R d)),
--             and R (ε d) maps R (L (R d)) to R d.

structure adjunction_unit {C D : category} (L : functor C D) (R : functor D C)
(η : natural_transformation (𝟙 C) (R⬝L)) (ε : natural_transformation (L⬝R) (𝟙 D)) :=
(id_L : ∀ (c : C), D.compose (ε.α (L c)) (L.map_hom (η.α c)) = D.id (L.map_obj c))
(id_R : ∀ (d : D), C.compose (R.map_hom (ε.α d)) (η.α (R d)) = C.id (R.map_obj d))

end category_theory
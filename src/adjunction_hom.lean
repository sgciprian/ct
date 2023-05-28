import .category
import .functors

namespace category_theory

-- Definition 2.1 https://ncatlab.org/nlab/show/adjoint+functor
-- in terms of natural bijections of hom-sets. (Mac Lane pg. 80)

-- L and R are the left adjoint and right adjoint functors, respectively.
-- Note that functor_map morphs a morphism via a functor,
-- while the object morph via a functor is done with a function application
-- as functor is coerced to a function that morphs the objects
-- (eg. L c for functor L : C → D and object c : C).

-- The naturality conditions are defined for all pairs ⟨c, d⟩ of objects and
-- arbitrary morphism dₕ in 𝒟(L c, d).

-- Naturality in c means this diagram commutes for all morphisms h : 𝒞(c', c):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--   (∘L h) ↓           ↓ (∘h)
--
--   𝒟(L c', d) → 𝒞(c', R d)
--              φ

structure adjunction {C D : category} (L : functor C D) (R : functor D C) (φ : Π {c : C} {d : D}, (D.hom (L c) d) → (C.hom c (R d))) :=

-- Homset mapping should be isomorphic.
(bijectivity : ∀ (c : C) (d : D), function.bijective (@φ c d))

-- Naturality in c means this diagram commutes for all morphisms h : 𝒞(c', c):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--   (∘L h) ↓           ↓ (∘h)
--
--   𝒟(L c', d) → 𝒞(c', R d)
--              φ
(naturality_c : ∀ (c : C) (d : D) (dₕ : D.hom (L c) d),
              ∀ {c' : C} (h : C.hom c' c), C.compose (φ dₕ) h = φ (D.compose dₕ (functor_map L h)))
              
-- While naturality in d means this diagram commutes for all morphisms k : 𝒟(d, d'):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--   (∘k) ↓           ↓ (∘R k)
--
--   𝒟(L c, d') → 𝒞(c, R d')
--              φ
(naturality_d : ∀ (c : C) (d : D) (dₕ : D.hom (L c) d),
              ∀ {d' : D} (k : D.hom d d'), C.compose (functor_map R k) (φ dₕ) = φ (D.compose k dₕ))

end category_theory
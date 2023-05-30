import category
import functors

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
structure adjunction_hom {C D : category} (L : functor C D) (R : functor D C) :=
(φ : Π {c : C} {d : D}, (D.hom (L c) d) → (C.hom c (R d)))

-- Homset mapping should be isomorphic.
(φr : Π {c : C} {d : D}, (C.hom c (R d)) → (D.hom (L c) d))
(sect : ∀ {c : C} {d : D} (h : C.hom c (R d)), (φ ∘ φr) h = h)
(retr : ∀ {c : C} {d : D} (k : D.hom (L c) d), (φr ∘ φ) k = k)

-- Naturality in c means this diagram commutes for all morphisms h : 𝒞(c', c):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--   (∘L h) ↓           ↓ (∘h)
--
--   𝒟(L c', d) → 𝒞(c', R d)
--              φ
(naturality_c : ∀ (c : C) (d : D) (dₕ : D.hom (L c) d),
              ∀ {c' : C} (h : C.hom c' c), C.compose (φ dₕ) h = φ (D.compose dₕ (L.map_hom h)))

-- While naturality in d means this diagram commutes for all morphisms k : 𝒟(d, d'):
--              φ
--   𝒟(L c,  d) → 𝒞(c,  R d)
--
--     k ↓           ↓ R k
--
--   𝒟(L c, d') → 𝒞(c, R d')
--              φ
(naturality_d : ∀ (c : C) (d : D) (dₕ : D.hom (L c) d),
              ∀ {d' : D} (k : D.hom d d'), C.compose (R.map_hom k) (φ dₕ) = φ (D.compose k dₕ))

-- Since the mapping is isomorphic, we also have duals for the naturality properties, where
-- the arrow corresponding to φ is reversed.
--
-- ∀ h : 𝒞(c', c):
--              φr
--   𝒞(c,  R d) → 𝒟(L c,  d)
--
--   (∘h) ↓            ↓ (∘L h)
--
--   𝒞(c', R d) → 𝒟(L c', d)
--              φr
(naturality_cr : ∀ (c : C) (d : D) (cₕ : C.hom c (R d)),
              ∀ {c' : C} (h : C.hom c' c), D.compose (φr cₕ) (L.map_hom h) = φr (C.compose cₕ h))

--
-- ∀ k : 𝒟(d, d'):
--              φr
--   𝒞(c,  R d) → 𝒟(L c,  d)
--
--   R k ↓            ↓ k
--
--   𝒞(c, R d') → 𝒟(L c, d')
--              φr
(naturality_dr : ∀ (c : C) (d : D) (cₕ : C.hom c (R d)),
              ∀ {d' : D} (k : D.hom d d'), D.compose k (φr cₕ) = φr (C.compose (R.map_hom k) cₕ))

end category_theory
import .category
import .functors
import .natural_transformation
import .adjunction_hom

namespace category_theory

-- Definition 2.3 https://ncatlab.org/nlab/show/adjoint+functor
-- in terms of unit η / counit ε (Mac Lane pg. 83, Theorem 2 (v))

-- 𝒞 and 𝒟 are two categories with L : 𝒞 → 𝒟 and R : 𝒟 → 𝒞 functors.
-- Then L and R are a pair of adjoint functors (L left adjoint, R right adjoint)
-- L ⊣ R, if we have natural transformations η, ε that fulfill the triangle identities
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
structure adjunction_unit {C D : category} (L : functor C D) (R : functor D C) :=
(η : natural_transformation (𝟙 C) (R⬝L))
(ε : natural_transformation (L⬝R) (𝟙 D))
(id_L : ∀ (c : C), D.compose (ε.α (L c)) (L.map_hom (η.α c)) = D.id (L.map_obj c))
(id_R : ∀ (d : D), C.compose (R.map_hom (ε.α d)) (η.α (R d)) = C.id (R.map_obj d))

-- Convert an adjunction defined via homset bijection to unit-counit adjunction
def adjunction_hom_to_unit {C D} {L : functor C D} {R} (a : adjunction L R)
: adjunction_unit L R :=
{
  -- the unit η can be constructing by using φ c on the identity morphism for L c,
  -- mapping 𝒟(L c, L c) to 𝒞(c, R (L c)), which is exactly a mapping made by a 
  -- natural transformation from Id C to R⬝L.
  η := {
    -- we construct the map as explained above
    α := λ c, by exact a.φ (D.id (L c)),
    -- and prove that it preserves the naturality condition
    naturality_condition := 
      begin
        intros c' c h,
        erw a.naturality_d,            -- use naturality in 𝒟
        erw D.left_id,                 -- eliminate id
        rw ← D.right_id (L.map_hom h), -- introduce id on other side
        erw a.naturality_c,            -- use naturality in 𝒞
        refl,
      end,
  },
  -- the counit ε can be constructed in a similar manner to the unit, by taking the
  -- inverse of the φ bijection (φr) and mapping 𝒞(R d, R d) to 𝒟(L (R d), d).
  -- (a natural transformation from L⬝R to Id D).
  ε := {
    α := λ d, by exact a.φr (C.id (R d)),
    -- proof is analogous (also dual) to η
    naturality_condition :=
      begin
        intros d d' g,
        apply symm,
        erw a.naturality_cr,
        erw C.right_id,
        rw ← C.left_id (R.map_hom g),
        erw adjunction.naturality_dr,
        refl,
      end,
  },
  -- All that is left to do is prove the triangle identities.
  id_L :=
    begin
      intro c,
      simp,
      erw a.naturality_cr,
      erw C.right_id,
      apply a.retr,
    end,
  id_R := 
    begin
      intro d,
      simp,
      erw a.naturality_d,
      erw D.left_id,
      apply a.sect,
    end,
}

-- Mac Lane pg. 82, Theorem 1 (6), (7)
def adjunction_unit_to_hom {C D} {L : functor C D} {R} (a : adjunction_unit L R) : adjunction L R :=
{
  -- φ(k)  = R k ∘ η c
  φ  := λ {c d} (k : D.hom (L c) d), C.compose (R.map_hom k) (a.η.α c),
  -- φr(h) = ε d ∘ L h
  φr := λ {c d} (h : C.hom c (R d)), D.compose (a.ε.α d) (L.map_hom h),
  sect := λ {c d} (h : C.hom c (R d)),
    begin
      simp,
      -- ⊢ R (ε d ∘ L h) ∘ η c = h
      rw R.comp (L.map_hom h) (a.ε.α d), -- un-distribute R
      -- ⊢ (R ε d ∘ R L h) ∘ η c = h
      rw ← C.assoc,                      -- change parantheses
      -- ⊢ R ε d ∘ (R L h ∘ η c) = h
      erw a.η.naturality_condition,      -- using η naturality
      -- ⊢ R ε d ∘ (η R d ∘ h) = h
      erw C.assoc,                       -- change parantheses again for Lean
      -- ⊢ (R ε d ∘ η R d) ∘ h = h
      erw a.id_R,
      -- ⊢ h = h - well, not actually this, but equivalent to it
      erw C.right_id,
      refl,
    end,
  retr := λ {c d} (k : D.hom (L c) d),
      begin
      simp,
      -- analogous (dual!!) to section
      rw L.comp,
      rw D.assoc,
      erw ← a.ε.naturality_condition,
      erw ← D.assoc,
      erw a.id_L,
      erw D.left_id, 
      refl,
      end,
  naturality_c :=
    begin
      intros,
      rw ← C.assoc,
      erw ← a.η.naturality_condition,
      rw C.assoc,
      erw ← R.comp,
    end,
  naturality_d :=
    begin
      intros,
      rw C.assoc,
      rw R.comp,
    end,
  -- dual to naturality_d
  naturality_cr :=
    begin
      intros,
      rw ← D.assoc,
      rw L.comp,
    end,
  -- dual to naturality_c
  naturality_dr :=
    begin
      intros,
      rw D.assoc,
      erw a.ε.naturality_condition,
      rw ← D.assoc,
      erw L.comp,
      refl,
    end,
}

end category_theory
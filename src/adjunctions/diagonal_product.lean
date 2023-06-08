import category
import adjunctions.homset
import functors.product
import functors.diagonal

namespace category_theory

-- Constructing the adjunction structure for Δ⊣×.
-- Δ is a functor from C to C×C
-- × is a functor from C×C to C
def diagonal_product_adjoint (C : category) [has_all_products C]
: adjunction_hom (diagonal_functor C) (product_functor C) :=
{
  φ :=
  -- φ maps a morphism h (=⟨f,g⟩) in C×C from ⟨c,c⟩ to d (=⟨a,b⟩)
  -- into a morphism in C from c to ×d (=a×b).
  -- That's exactly what we defined as ps, applied to f and g.
    begin
      intros c d h,
      let f := h.fst,
      let g := h.snd,
      exact ps f g,
    end,
  φr :=
  -- φr maps a morphism in C from c to ×d (=a×b) into a 
  -- morphism in C×C from ⟨c,c⟩ to d (=⟨a,b⟩).
  -- We can deconstruct a×b into a and b via its projections
  -- getting morphisms from c to a and c to b which we merge
  -- into a morphism from ⟨c,c⟩ to ⟨a,c⟩ the obvious way.
    begin
      intros c d h,
      let axb := po d.fst d.snd,
      let ca := C.compose axb.p₁ h,
      let cb := C.compose axb.p₂ h,
      exact (ca, cb),
    end,
  sect :=
  -- φ is isomorphic (preserves structure)
  -- to prove: (φ ∘ φr) ∘ h = h
  -- that is, ps (πa ∘ h) (πb ∘ h) = h
  -- if πa is the morph from a×b to a.
    begin
      intros c d h,
      simp,
      let a := d.fst,
      let b := d.snd,
      -- Lean for some reason can't simplify (x, y).fst to x... so we spell it out for it
      suffices q : ps (C.compose (po d.fst d.snd).p₁ h) (C.compose (po d.fst d.snd).p₂ h) = h,
      exact q,
      -- both morphism in the ps are _ ∘ h, so we can change it to (ps _ _) ∘ h
      rw ← refl_ps_compose,
      -- and we have a ps with just the projections for a product, so it can be factored out
      rw simp_ps_id,
      rw C.right_id,
    end,
  retr :=
  -- φr is isomorphic
    begin
      intros c d h,
      simp,
      rw ← simp_ps_left,
      rw ← simp_ps_right,
      cases h,
      refl,
    end,
  naturality_c :=
    begin
      intros,
      simp,
      rw refl_ps_compose,
      rw refl_ps_pm,
      rw refl_ps_pm,
      rw simp_comp_left,
      split,
    end,
  naturality_d :=
    begin
      intros,
      simp,
      rw refl_ps_pm,
      rw C.assoc,
      rw refl_ps_pm,
      rw simp_comp_left,
      have q : (product_functor C).map_hom k = product_morphism k.fst k.snd,
      refl,
      rw q,
      apply product_of_composible_morphisms,
    end,
  naturality_cr :=
    begin
      intros,
      simp,
      have q : (diagonal_functor C).map_hom h = (h, h),
      refl,
      rw q,
      
    end,
  naturality_dr :=
    begin
      intros,
      simp,
      
    end,
}

end category_theory
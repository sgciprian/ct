import category
import adjunctions.homset
import functors.product
import functors.diagonal

namespace category_theory

-- Useful function that bundles c with two id c's, for use with c×c.
def id_bundle {C : category} [has_all_products C] (c : C) : binary_product_bundle c c :=
{
  x := c,
  x₁ := C.id c,
  x₂ := C.id c,
}

-- Apparently Lean needs to be able to figure out stuff...
@[simp]
lemma id_bundle_id₁ {C : category} [has_all_products C] (c : C) : (id_bundle c).x₁ = C.id c := by refl
@[simp]
lemma id_bundle_id₂ {C : category} [has_all_products C] (c : C) : (id_bundle c).x₂ = C.id c := by refl

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
  -- Deconstruct h as its left and right C-category morphisms
  -- then should be similar (but simpler) to proving section.
    begin
      intros c d h,
      simp,
      unfold pm,
      let ca := h.fst,
      let cb := h.snd,
      have q : (ca, cb) = h, simp,
      rw ← q,

      -- Showing left and right side are equal to ca and cb is identical to section. (t₂ and t₃ proofs)
      -- copy-pasted from there
      have q₁ := product_morphism_commutes (po c c) (po d.fst d.snd) ca cb, -- commuting diagram for (πa∘h)×(πb∘h)
      have q₂ := (po c c).ump (id_bundle c), -- by ump, (po c c).p₁ ∘ (unique morph from c to c×c) = id
      -- Proving πa side:
      have t₁ : C.compose (po d.fst d.snd).p₁ (C.compose (product_morphism ca cb) ((po c c).ue (id_bundle c))) = ca,
      rw C.assoc,   -- make it clear to lean that we intend to apply q₁
      rw ← q₁.left,
      rw ← C.assoc, -- help lean some more to replace the (po c c) stuff with just id
      rw ← q₂.left,
      simp,
      apply C.left_id, -- done!
      -- Now also for πb side, identical
      have t₂ : C.compose (po d.fst d.snd).p₂ (C.compose (product_morphism ca cb) ((po c c).ue (id_bundle c))) = cb,
      rw C.assoc,   -- make it clear to lean that we intend to apply q₁
      rw ← q₁.right,
      rw ← C.assoc, -- help lean some more to replace the (po c c) stuff with just id
      rw ← q₂.right,
      simp,
      apply C.left_id, -- done!
      -- end copy-paste

      rw t₁,
      rw t₂,
    end,
  naturality_c :=
    begin
      intros,
      simp,
      unfold pm,
    end,
}

end category_theory
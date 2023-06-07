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
  -- If we name α the unique morphism from c to c×c via two id's,
  -- it is clear the morphism we want is f×g ∘ α.
    begin
      intros c d h,
      let cxc := po c c,
      let axb := po d.fst d.snd,
      let f := h.fst,
      let g := h.snd,
      let fxg := pm cxc axb f g,
      let α := cxc.ue (id_bundle c),
      exact C.compose fxg α,
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
  -- that is, (πa ∘ h)×(πb ∘ h) ∘ α = h
  -- if πa is the morph from a×b to a,
  -- and α is the morph from c to c×c via id.
    begin
      intros c d h,
      simp,
      let axb := po d.fst d.snd,
      let ca := C.compose axb.p₁ h,
      let cb := C.compose axb.p₂ h,
      -- Showing that h is the unique morph from c to a×b
      -- mapping c to a by πa ∘ h and c to b by πb ∘ h.
      let b : binary_product_bundle d.fst d.snd :=
        {
          x := c,
          x₁ := ca,
          x₂ := cb,
        },
      have b₁ : b.x₁ = ca,refl,
      have b₂ : b.x₂ = cb,refl,
      have a₁ : axb.p₁ = (po d.fst d.snd).p₁,refl,
      have a₂ : axb.p₂ = (po d.fst d.snd).p₂,refl,
      have a : axb = po d.fst d.snd,refl,
      have t₁ : h = axb.ue b,
      apply axb.uu b h,
      split,refl,refl,
      rw t₁,
      -- Now we need to prove that πa ∘ (πa ∘ h)×(πb ∘ h) ∘ (πc ∘ α) = πa ∘ h
      -- and likewise πb ∘ (πb ∘ h)×(πb ∘ h) ∘ (πc ∘ α) = πa ∘ h.
      -- Then we can use this result to show (πa ∘ h)×(πb ∘ h) ∘ α
      -- is also the unique morph from c to a×b mapping c to a
      -- by πa ∘ h and c to b by πb ∘ h (well, something equal to it).
      have q₁ := product_morphism_commutes (po c c) axb ca cb, -- commuting diagram for (πa∘h)×(πb∘h)
      have q₂ := (po c c).ump (id_bundle c), -- by ump, (po c c).p₁ ∘ (unique morph from c to c×c) = id
      -- Proving πa side:
      have t₂ : C.compose (po d.fst d.snd).p₁ (C.compose (product_morphism ca cb) ((po c c).ue (id_bundle c))) = ca,
      rw C.assoc,   -- make it clear to lean that we intend to apply q₁
      rw ← q₁.left,
      rw ← C.assoc, -- help lean some more to replace the (po c c) stuff with just id
      rw ← q₂.left,
      simp,
      apply C.left_id, -- done!
      -- Now also for πb side, identical
      have t₃ : C.compose (po d.fst d.snd).p₂ (C.compose (product_morphism ca cb) ((po c c).ue (id_bundle c))) = cb,
      rw C.assoc,   -- make it clear to lean that we intend to apply q₁
      rw ← q₁.right,
      rw ← C.assoc, -- help lean some more to replace the (po c c) stuff with just id
      rw ← q₂.right,
      simp,
      apply C.left_id, -- done!
      -- Bringing it all together by invoking the uniquness of the map from c to a×b
      -- via πa ∘ h, πb ∘ h.
      unfold pm,
      rw ← axb.uu b (C.compose (product_morphism ca cb) ((po c c).ue (id_bundle c))),
      -- We have to prove that 1. (πa ∘ h)×(πb ∘ h) ∘ α satisfies the universal property
      --                       2. our construction via φ∘φr is indeed equal to our morph
      --                          (πa ∘ h)×(πb ∘ h) ∘ α.
      tactic.swap, -- choosing to prove (1.) first
      split,       -- first prove πa side, then πb side
      rw b₁,       -- replace b.x₁ with ca for lean
      symmetry,
      exact t₂,    -- we already proved this at t₂!    
      rw b₂,       -- same steps but for πb side
      symmetry,
      exact t₃,    -- now we only have proving (2.) left
      apply simp_comp_left,
      apply simp_product_morphism,
      split,
      exact t₂,
      exact t₃,
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
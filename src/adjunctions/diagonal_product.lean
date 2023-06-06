import category
import adjunctions.homset
import functors.product
import functors.diagonal

namespace category_theory

-- Useful function that bundles c with two id c's, for use with c×c.
def id_c_bundle {C : category} [has_all_products C] (c : C) : binary_product_bundle c c :=
{
  x := c,
  x₁ := C.id c,
  x₂ := C.id c,
}

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
      let α := cxc.ue (id_c_bundle c),
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
      let pa := axb.p₁,
      let pb := axb.p₂,
      let ca := C.compose pa h,
      let cb := C.compose pb h,
      exact (ca, cb),
    end,
  sect :=
  -- φ is a bijection
    begin
      intros,
      simp,
      let cxc := po c c,
      let axb := po d.fst d.snd,
      let b : binary_product_bundle d.fst d.snd :=
      {
        x := c,
        x₁ := C.compose axb.p₁ h,
        x₂ := C.compose axb.p₂ h,
      },
      let q := axb.uu b h,
      have t : b.x₁ = C.compose axb.p₁ h ∧ b.x₂ = C.compose axb.p₂ h,
      split,
      refl,
      refl,
      let q := q t,
      sorry,
    end,
  retr := sorry,
  naturality_c :=
    begin
      intros,
      simp,
      
    end,
}

end category_theory
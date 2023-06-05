import category
import adjunctions.unit_counit
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

-- Useful function that constructs a morphism from c → c×c for c ∈ C₀.
-- We use c×c's existence of a morph from all x in C that have
-- morphisms from x to c and apply it to c → c×c.
def from_c_to_product_c_c {C : category} [has_all_products C] (c : C) : C.hom c (po c c).p :=
    -- making the bundle of c and (two) morphism to c
    -- and using the product object's universal existence property
    -- to construct a morphism from c to c×c
    by exact (po c c).ue (id_c_bundle c)

-- Constructing the adjunction structure for Δ⊣×.
-- Δ is a functor from C to C×C
-- × is a functor from C×C to C
def diagonal_product_adjoint (C : category) [has_all_products C]
: adjunction_unit (diagonal_functor C) (product_functor C) :=
{
  -- Unit is a natural transformation from Id C to ×Δ.
  η :=
  {
    -- It supplies a morphism from Id c to (× ∘ Δ) c, ∀ c ∈ C₀.
    -- As Id c = c and × (Δ c) = × ⟨c,c⟩ = c×c, we require a
    -- morphism from c to c×c. 
    α := from_c_to_product_c_c,
    -- For it to be natural, we have to prove that for all morphisms
    -- f in C from x to y, (×Δ f) ∘ (α x) = (α y) ∘ (Id f).
    -- This is equivalent to f×f ∘ (α x) = (α y) ∘ f.
    naturality_condition :=
      begin
        intros x y f,
        let xx := po x x,
        let yy := po y y,
        let ff := pm xx yy f f,
        -- Using the proof that product morphism commute, we get
        -- f ∘ πx = πy ∘ f×f (where πx is the obvious morph from x×x to x).
        let h₁ := (product_morphism_commutes xx yy f f).left,
        let α := from_c_to_product_c_c,
        -- Left-composing with (α y) eliminates πy and we have
        -- (α y) ∘ f ∘ πx = f×f.
        have h₂ : C.compose (α y) (C.compose f xx.p₁) = ff,
        rw h₁,        -- (α y) ∘ (πy ∘ f×f) = f×f
        rw C.assoc,   -- ((α y) ∘ πy) ∘ f×f = f×f
        -- Now proving πy ∘ (α y) = Id y, this comes via the construction
        -- of α (the unique morphism from c to c×c via Id c's).
        have y_id : C.compose yy.p₁ (α y) = C.id y,
        let q := (yy.ump (id_c_bundle y)).left,
        symmetry,
        exact q, -- proved!
        -- Proving (α y) ∘ πy = Id y×y via the ump of y×y (both 
        have yy_id : C.compose (α y) yy.p₁ = C.id yy.p,
        rw identity_morphism_of_product,
        let q := (product_morphism_commutes yy yy (C.id y) (C.id y)).left,
        rw C.right_id at q,
        sorry,
        sorry,
        have h₃ : C.compose (α y) f = C.compose ff (α x),
        sorry,
        symmetry,
        exact h₃,
      end,
  }
}

end category_theory
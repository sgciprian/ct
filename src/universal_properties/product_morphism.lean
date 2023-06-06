import functors.functor
import universal_properties.binary_product

namespace category_theory

-- Constructs the bundle of cxi with its morphisms to d and j via c and i
--       c ← cxi → i
--
--     f ↓         ↓ g
--
--       d         j
def product_morphism_bundle {C : category} {c d i j : C} (cxi : binary_product c i)
(f : C.hom c d) (g : C.hom i j) : binary_product_bundle d j :=
{
  x := cxi.p,
  x₁ := C.compose f cxi.p₁,
  x₂ := C.compose g cxi.p₂,
}

-- Via the universal property and with the bundle defined above, there is a mapping from cxi to dxj.
def product_morphism {C : category} {c d i j : C} {cxi : binary_product c i} {dxj : binary_product d j}
(f : C.hom c d) (g : C.hom i j)
: C.hom cxi.p dxj.p := dxj.ue (product_morphism_bundle cxi f g)

-- Short-hand for the f×g.
def pm {C : category} {c d i j : C} (cxi : binary_product c i) (dxj : binary_product d j)
(f : C.hom c d) (g : C.hom i j) : C.hom cxi.p dxj.p := @product_morphism C c d i j cxi dxj f g

--       c ←   c×i   → i
--              |
--     f ↓  f×g |    ↓ g   commutes
--              ↓
--       d ←   d×j   → j
lemma product_morphism_commutes {C : category} {c d i j : C}
(cxi : binary_product c i) (dxj : binary_product d j) (f : C.hom c d) (g : C.hom i j)
: C.compose f cxi.p₁ = C.compose dxj.p₁ (product_morphism f g) 
∧ C.compose g cxi.p₂ = C.compose dxj.p₂ (product_morphism f g) :=
  begin
    -- Use the construction of the product morphism.
    unfold product_morphism,
    -- Split into the left and right squares of the diagram.
    split,
    -- Using the definition of the mapping property, we get proofs of the commuting diagrams.
    apply (dxj.ump (product_morphism_bundle cxi f g)).left,
    apply (dxj.ump (product_morphism_bundle cxi f g)).right,
  end

-- Proving id c×d = (id c) × (id d).
lemma identity_morphism_of_product {C : category} {c d : C} (cxd : binary_product c d)
: C.id cxd.p = product_morphism (C.id c) (C.id d) :=
  begin
    -- We have two morphisms from c×d to c×d : C.id c×d and (C.id c)×(C.id d).
    -- We're using the uniqueness property of product c×d to show that C.id c×d, a morph
    -- from c×d to c×d, is same as (C.id c)×(C.id d), a preexisting morph between the same objects.
    --
    -- b is a bundle containing c×d and its two maps to c and d (the identities).
    let b := product_morphism_bundle cxd (C.id c) (C.id d),
    apply cxd.uu b (C.id cxd.p),
    -- So now what we need to prove is essentially that C.id (p₁ c×d) = p₁ (C.id c×d)
    -- (projecting the identity of c×d to c is identical to the identity of projecting c×d to c),
    -- trivial. We just need to swap around the C.id's to make Lean figure out the two definitions
    -- are identical.
    split,
    rw C.left_id cxd.p₁,
    rw ← C.right_id cxd.p₁,
    refl,
    rw C.left_id cxd.p₂,
    rw ← C.right_id cxd.p₂,
    refl,
  end

-- Proving that the product of two composed morphisms is the composition of two product morphisms.
-- For f, f', g, g' morphisms for which g∘f and g'∘f' makes sense, and their domains, codomains
-- admit products in C.
-- So prove that the "direct" morph from c×c' to e×e', (g∘f)×(g'∘f'), is equal to the composite:
-- (g×g')∘(f×f').
--       c ←   c×c'   → c'                            c ←   c×c'   → c'
--              |                                            |
--     f ↓  ff' |       ↓ f'                          ↓      |      ↓
--              ↓                                            |
--       d ←   d×d'   → d'   and if we ignore d,  g∘f ↓    × |      ↓ g'∘f'
--              |                                            |
--     g ↓  gg' |       ↓ g'                          ↓      |      ↓
--              ↓                                            ↓
--       e ←   e×e'   → e'                            e ←   e×e'  → e'
lemma product_of_composible_morphisms {C : category} {c c' d d' e e' : C}
{cp : binary_product c c'} {dp : binary_product d d'} {ep : binary_product e e'}
(f : C.hom c d) (f' : C.hom c' d') (g : C.hom d e) (g' : C.hom d' e')
: C.compose (pm dp ep g g') (pm cp dp f f') = pm cp ep (C.compose g f) (C.compose g' f') :=
  begin
    -- Strategy: use the uniqueness property of e×e' to show that (g∘f)×(g'∘f') = (f×f')∘(g×g').
    -- To do that, we need to show that (f×f')∘(g×g') is also a product of morphisms from c×c' to e×e'.
    -- So, prove that 1. (f×f')∘(g×g') is a morph from c×c' to e×e' (obvious);
    --                2. g∘f maps c to e and g'∘f' maps c' to e' (obvious);
    --                3. (f×f')∘(g×g') makes the diagram for product of morphisms commute.
    -- For (3.), that means we have to show g ∘ f ∘ πc = πe (f×f')∘(g×g') and
    --                                      g'∘ f'∘ πc'= πe'(f×f')∘(g×g'), where πa maps a×a' to a.
    -- We have the two commuting diagrams from cxc' → d×d' and d×d' → e×e',
    -- which means f ∘ πc = πd ∘ (f×f') and f'∘πc' = πd'∘(f×f') (h₁)
    -- and g ∘ πd = πe ∘ (g×g') and g'∘πd' = πe'∘(g×g') (h₂).
    have cp_dp_comm := product_morphism_commutes cp dp f f',
    cases cp_dp_comm,
    have dp_ep_comm := product_morphism_commutes dp ep g g',
    cases dp_ep_comm,
    have h₁ : C.compose f cp.p₁ = C.compose dp.p₁ (pm cp dp f f') ∧ C.compose f' cp.p₂ = C.compose dp.p₂ (pm cp dp f f'),
    split,
    exact cp_dp_comm_left,
    exact cp_dp_comm_right,
    have h₂ : C.compose g dp.p₁ = C.compose ep.p₁ (pm dp ep g g') ∧ C.compose g' dp.p₂ = C.compose ep.p₂ (pm dp ep g g'),
    split,
    exact dp_ep_comm_left,
    exact dp_ep_comm_right,
    -- Now bringing these two together, we can prove that g ∘ f ∘ πc = πe (f×f')∘(g×g') (q₁)
    -- and g'∘ f'∘ πc'= πe'(f×f')∘(g×g') (q₂).
    have q₁ : C.compose g (C.compose f cp.p₁) = C.compose ep.p₁ (C.compose (pm dp ep g g') (pm cp dp f f')),
    rw h₁.left,    -- g ∘ πd ∘ (f×f') = πe (f×f')∘(g×g') via h₁
    rw C.assoc,    -- rewrite to (g ∘ πd) ∘ (f×f') = πe (f×f')∘(g×g') via associativity
    rw h₂.left,    -- (πe ∘ (g×g')) ∘ (f×f') = πe (f×f')∘(g×g') via h₂
    symmetry,      -- rewrite to πe (f×f')∘(g×g') = (πe ∘ (g×g')) ∘ (f×f') so it fits
    apply C.assoc, -- with the associativity rule for morphism composition and we're done.
    have q₂ : C.compose g' (C.compose f' cp.p₂) = C.compose ep.p₂ (C.compose (pm dp ep g g') (pm cp dp f f')),
    rw h₁.right,
    rw C.assoc,
    rw h₂.right,
    symmetry,
    apply C.assoc,
    -- This leaves us with applying the uniqueness property of e×e' and showing that (f×f')∘(g×g')
    -- fulfills (3.).
    apply ep.uu (product_morphism_bundle cp (C.compose g f) (C.compose g' f')) (C.compose (pm dp ep g g') (pm cp dp f f')),
    split,
    rw ← q₁,
    rw C.assoc,
    refl,
    rw ← q₂,
    rw C.assoc,
    refl,
  end

-- help lean some more
@[simp]
lemma simp_product_morphism {C : category} {c c' d d' : C} {cp : binary_product c c'} {dp : binary_product d d'}
{f f' : C.hom c d} {g g' : C.hom c' d'}
: f = f' ∧ g = g' → @product_morphism C c d c' d' cp dp f g = product_morphism f' g' :=
  begin
    cc,
  end

end category_theory
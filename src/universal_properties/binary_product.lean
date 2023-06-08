import functors.functor

namespace category_theory

-- There is already a definition for binary product in the root folder,
-- but it uses ∃ which leads to classical reasoning to get the actual object
-- out of exists.

-- Defines an object in C that has morphisms to two other (specific) objects.
structure binary_product_bundle {C : category} (c d : C) :=
(x : C)
(x₁ : C.hom x c)
(x₂ : C.hom x d)

-- Defines the binary product and its properties for two (specific) objects in C.
structure binary_product {C : category} (c d : C) :=
-- product p is made up of the actual object and its two morphisms
(p : C)
(p₁ : C.hom p c)
(p₂ : C.hom p d)
-- for all other objects x with morphisms to same objects, there is a unique morphism
-- mapping it to p that makes the two triangles in the diagram commute:
--             x
--          ↙  ↓  ↘ 
--        c  ← p →  d 
-- Existence
(ue : Π (x : binary_product_bundle c d), C.hom x.x p)
(ump : ∀ (x : binary_product_bundle c d), x.x₁ = C.compose p₁ (ue x) ∧ x.x₂ = C.compose p₂ (ue x))
-- Uniqueness
(uu : ∀ (x : binary_product_bundle c d) (h : C.hom x.x p), x.x₁ = C.compose p₁ h ∧ x.x₂ = C.compose p₂ h → h = ue x)

def bundle {C : category} {c d : C} (p : binary_product c d) : binary_product_bundle c d :=
{
  x := p.p,
  x₁ := p.p₁,
  x₂ := p.p₂,
}

-- Category with binary products for all pairs of objects.
class has_all_products (C : category) :=
(product : Π (c d : C), binary_product c d)

-- Short-hand for the c×d.
def po {C : category} [has_all_products C] (c d : C) := has_all_products.product c d

-- Short-hand for the unique morphism going from c to a×b via f and g.
-- c → a×b, f g
def ps {C : category} [has_all_products C] {c a b : C} (f : C.hom c a) (g : C.hom c b) := (po a b).ue {x := c, x₁ := f, x₂ := g}

-- Makes (unique) morphism from c to c×c via identities.
def mk_prod {C : category} [has_all_products C] (c : C) : C.hom c (po c c).p :=
  (po c c).ue {x := c, x₁ := C.id c, x₂ := C.id c}

-- Some useful simplification rules.
-- Composing the projection arrows with the c → c×c morph does nothing.
lemma simp_mk_prod_left {C : category} [has_all_products C] (c : C)
: C.compose (po c c).p₁ (mk_prod c) = C.id c :=
  begin
    unfold mk_prod,
    have q := (po c c).ump {x := c, x₁ := C.id c, x₂ := C.id c},
    simp at q,
    symmetry,
    exact q.left,
  end

lemma simp_mk_prod_right {C : category} [has_all_products C] (c : C)
: C.compose (po c c).p₂ (mk_prod c) = C.id c :=
  begin
    unfold mk_prod,
    have q := (po c c).ump {x := c, x₁ := C.id c, x₂ := C.id c},
    simp at q,
    symmetry,
    exact q.right,
  end

-- f = πa ∘ (c → a×b, f g), where πa is the projection from a×b to a
lemma simp_ps_left {C : category} [has_all_products C] {c a b : C} (f : C.hom c a) (g : C.hom c b)
: f = C.compose (po a b).p₁ (ps f g) :=
  begin
    -- Just use the universal mapping property of a×b.
    unfold ps,
    have q := (po a b).ump {x := c, x₁ := f, x₂ := g},
    rw ← q.left,
  end

-- g = πb ∘ (c → a×b, f g)
lemma simp_ps_right {C : category} [has_all_products C] {c a b : C} (f : C.hom c a) (g : C.hom c b)
: g = C.compose (po a b).p₂ (ps f g) :=
  begin
    -- Identical to simp_ps_left
    unfold ps,
    have q := (po a b).ump {x := c, x₁ := f, x₂ := g},
    rw ← q.right,
  end

-- If we have a ps with the two projection arrows, then that's just identity
lemma simp_ps_id {C : category} [has_all_products C] {a b : C} : ps (po a b).p₁ (po a b).p₂ = C.id (po a b).p :=
  begin
    -- Since both identity and the ps are morphs from a×b to a×b via πa and πb
    have q := (po a b).uu {x := (po a b).p, x₁ := (po a b).p₁, x₂ := (po a b).p₂} (C.id (po a b).p),
    simp at q,
    have r := (po a b).uu {x := (po a b).p, x₁ := (po a b).p₁, x₂ := (po a b).p₂} (ps (po a b).p₁ (po a b).p₂),
    simp at r,
    rw q,
    rw r,
    -- And now we just have to show that neither composing with ps πa πb nor identity changes anything - trivial.
    split,
    apply simp_ps_left,
    apply simp_ps_right,
    split,
    rw C.left_id,
    rw C.left_id,
  end

-- Composition can go inside the ps.
-- (c → a×b, f g) ∘ h = (c' → a×b, f∘h g∘h)
lemma refl_ps_compose {C : category} [has_all_products C] {c' c a b : C} (h : C.hom c' c) (f : C.hom c a) (g : C.hom c b)
: C.compose (ps f g) h = ps (C.compose f h) (C.compose g h) :=
  begin
    -- Here, since (c → a×b, fg) ∘ h is an arrow from c' to a×b, if we show that
    -- it maps c' to a via f∘h and c' to b via g∘h then it must be identical to (c' → a×b, f∘h g∘h).
    have q := (po a b).uu {x := c', x₁ := C.compose f h, x₂ := C.compose g h} (C.compose (ps f g) h),
    simp at q,
    apply q,
    split,
    -- Now showing f∘h = πa ∘ (c → a×b, fg) ∘ h.
    rw C.assoc,
    apply simp_comp_left,
    apply simp_ps_left,
    -- The πb side.
    rw C.assoc,
    apply simp_comp_left,
    apply simp_ps_right,
  end

end category_theory
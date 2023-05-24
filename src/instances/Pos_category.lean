import category
import poset
-- We import this ↓ to help with subtypes in proofs.
import data.subtype

open category_theory

-- Pos
-- category of posets
def Pos : category :=
{
  -- Each object in this category is a whole poset.
  C₀ := poset_u,

  -- Morphisms between posets are functions defined on the
  -- underlying sets (care, x : X means x is of type X.memb)
  -- that preserve the ordering.
  hom := λ X Y, {f : X → Y // ∀ (x y : X), x ≤ y → (f x) ≤ (f y)},

  -- Now for identity, we will prove that the identity function
  -- preserves the ordering.
  -- The ⟨ ⟩ brackets denote an anonymous constructor, in this
  -- case, a pair (actually a subtype) containing the function
  -- and the proof (Prop) that it is order-preserving.
  id  := λ X, ⟨id, begin
      intros x y h,
      rw id, rw id,
      exact h,
    end⟩,

  -- This proof is straightforward, as long as we remember
  -- that f and g are pairs; f.val is the function and
  -- f.property the proof that it preserves the order.
  -- Then the composition is just function composition.
  -- ↑f is equivalent to f.val, and introduced by `simp`.
  compose := λ X Y Z g f, ⟨g.val ∘ f.val,
    begin
      intros x y h,
      simp,
      have fp := f.property,
      have gp := g.property,
      apply gp,
      apply fp,
      exact h,
    end⟩,

  -- As Prop is proof-irrelevant, that if both p and q prove
  -- the same Prop, then ⟨f, p⟩ is essentially identical to
  -- ⟨f, q⟩. This is also what Lean does here, substituting
  -- the proof of preserving the order with a wildcard _; it
  -- does not matter what the proof is, at long as it exists.

  -- However, Lean is also a bit too smart for us, since it
  -- automagically coerces the bundled types to the function
  -- in them, and then it's just a matter of applying a few
  -- identity or associativity lemmas.
  left_id :=
    begin
      simp,
    end,
  right_id :=
    begin
      simp,
    end,
  assoc :=
    begin
      intros,
      simp,
    end,
}

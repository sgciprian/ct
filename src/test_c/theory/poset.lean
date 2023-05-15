import test_c.theory.preorder
namespace ct

universe u

class poset (α : Type u) extends preorder α :=
(antisymm  : ∀ (x y : α), x ≤ y ∧ y ≤ x → x = y)
-- done with class

class poset_morph {α β : Type u} (proof_α : poset α) (proof_β : poset β) :=
(f : α → β)
(prop : ∀ x₁ x₂ : α, x₁ ≤ x₂ → (f x₁) ≤ (f x₂))
-- done with class

instance poset_id {α : Type u} (proof_α : poset α) : poset_morph proof_α proof_α :=
{
  f := id,
  prop :=
    begin
      intros x₁ x₂ h,
      rw id,
      rw id,
      exact h,
    end,
}

end ct
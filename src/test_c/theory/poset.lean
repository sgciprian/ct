import test_c.theory.preorder
namespace ct

class poset (α : Type*) extends preorder α :=
(antisymm  : ∀ (x y : α), x ≤ y ∧ y ≤ x → x = y)
-- done with class

class poset_morph {α β : Type*} (proof_α : poset α) (proof_β : poset β) (f : α → β) :=
(prop : ∀ x₁ x₂ : α, x₁ ≤ x₂ → (f x₁) ≤ (f x₂))
-- done with class

instance poset_id {α : Type*} (proof_α : poset α) : poset_morph proof_α proof_α id :=
{
  prop :=
    begin
      intros x₁ x₂ h,
      rw id,
      rw id,
      exact h,
    end,
}

instance poset_compose {α β γ: Type*} {pα : poset α} {pβ : poset β} {pγ : poset γ} {f : α → β} {g : β → γ} (m₂ : poset_morph pβ pγ g) (m₁ : poset_morph pα pβ f) : poset_morph pα pγ (g ∘ f) :=
{
  prop :=
    begin
      intros x₁ x₂ h,
      have m₁ := m₁.prop,
      have m₂ := m₂.prop,
      specialize m₁ x₁ x₂ h,
      specialize m₂ (f x₁) (f x₂) m₁,
      exact m₂,
    end, 
}

end ct
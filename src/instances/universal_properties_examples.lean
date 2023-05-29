import universal_properties
import .Set_category

namespace category_theory

lemma empty_set_initial_in_Set : isInitial Set empty :=
begin
  intros B f g,
  funext x, -- Proving functions equality pointwise
  cases x, -- There are no elements in the empty set, so we can use cases to handle all possible cases (i.e., none)
end

lemma singleton_terminal_in_Set (b : Set.C₀) (h : subsingleton b) : isTerminal Set b :=
begin
  intros A f g,
  funext a, -- Proving functions equality pointwise
  apply subsingleton.elim (f a) (g a), -- Using the subsingleton property to conclude f a = g a
end

lemma binary_product_in_Set (A B : Set.C₀) : isBinaryProduct Set (A × B) (λ p, p.1) (λ p, p.2) :=
begin
  intros Q q₁ q₂,
  let f : Q → A × B := λ x, (q₁ x, q₂ x),
  have map_proj₁ : ∀ (x : Q), (λ p : A × B, p.1) (f x) = q₁ x,
  {
    intro x,
    simp [f],
  },
  have map_proj₂ : ∀ (x : Q), (λ p : A × B, p.2) (f x) = q₂ x,
  {
    intro x,
    simp [f],
  },
  existsi f,
  split,
  {
    split,
    {
      apply funext,
      intro x,
      exact (map_proj₁ x),
    },
    {
      apply funext,
      intro x,
      exact (map_proj₂ x),
    },
  },
  {
    intros g H,
    apply funext,
    intro x,
    cases H with H₁ H₂,
    have H₁' : (λ (p : A × B), p.1) (g x) = q₁ x,
    {
      rw ←H₁,
      refl,
    },
    have H₂' : (λ (p : A × B), p.2) (g x) = q₂ x,
    {
      rw ←H₂,
      refl,
    },
    simp [f],
    rw ←H₁', 
    rw ←H₂', 
    simp [H₁', H₂'],
  },
end

lemma binary_coproduct_universal_property (A B : Set.C₀) : isBinaryCoproduct Set (A ⊕ B) sum.inl sum.inr :=
begin
  intros D i₁ i₂,
  let f : (A ⊕ B) → D := λ x, sum.cases_on x i₁ i₂,
  have map_inl : ∀ (x : A), f (sum.inl x) = i₁ x,
  {
    intro x,
    simp [f],
  },
  have map_inr : ∀ (x : B), f (sum.inr x) = i₂ x,
  {
    intro x,
    simp [f],
  },
  existsi f,
  split,
  {
    split,
    {
      apply funext,
      intro x,
      exact (map_inl x),
    },
    {
      apply funext,
      intro x,
      exact (map_inr x),
    },
  },
  {
    intros g H,
    apply funext,
    intro x,
    cases x,
    {
      have H₁' : (λ (p : A ⊕ B), g p) (sum.inl x) = i₁ x,
      {
        rw ←H.1,
        refl,
      },
      change (g (sum.inl x)) with ((λ (p : A ⊕ B), g p) (sum.inl x)),
      rw H₁',
    },
    {
      have H₂' : (λ (p : A ⊕ B), g p) (sum.inr x) = i₂ x,
      {
        rw ←H.2,
        refl,
      },
      change (g (sum.inr x)) with ((λ (p : A ⊕ B), g p) (sum.inr x)),
      rw H₂',
    },
  },
end

end category_theory
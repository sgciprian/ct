import .category

namespace category_theory

-- A monoid is a triple (M, m, e). Here M is implicitly C.C₀
class monoid (C : category) :=
  (m : C.C₀ → C.C₀ → C.C₀)
  (e : C.C₀)
  (assoc : ∀ (X Y Z : C.C₀), m X (m Y Z) = m (m X Y) Z)
  (left_id : ∀ (X : C.C₀), m X e = X)
  (right_id : ∀ (X : C.C₀), m e X = X)


end category_theory
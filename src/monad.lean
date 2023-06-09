import functors
import natural_transformation

namespace category_theory
  
  structure Monad {C : category} (T : C => C) :=
    (μ : natural_transformation (T ⬝ T) T)
    (η : natural_transformation (Id C) T)
    (assoc : ∀ X : C.C₀, (μ ⊚ μ × (ID T)).α X = (μ ⊚ (ID T) × μ).α X)
    (lu : ∀ X : C.C₀, (μ ⊚ ID T × η).α X = (ID T).α X)
    (ru : ∀ X : C.C₀, (μ ⊚ η × ID T).α X = (ID T).α X)
  
end category_theory

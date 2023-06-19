import functors
import natural_transformation

namespace category_theory
  
  structure Monad {C : category} (T : C => C) :=
    (μ : (T ⬝ T) ==> T)
    (η : (Id C) ==> T)
    (assoc : μ ⊚ μ × (ID T) = μ ⊚ (ID T) × μ ⊚ (assoc_nt T T T))
    (lu : μ ⊚ ID T × η = ID T ⊚ right_unit_nt T)
    (ru : μ ⊚ η × ID T = ID T ⊚ left_unit_nt T)
  
end category_theory

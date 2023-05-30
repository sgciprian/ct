import natural_transformation
import functors

namespace category_theory
  
  structure Monad {C : category} (T : functor C C) :=
    (T₂ : functor C C)
    (μ : natural_transformation T₂ T)
    (η : natural_transformation I T)
    (assoc : comp (μ mul id) μ = comp μ (id mul id))
    (lu)
    (ru)

end category_theory

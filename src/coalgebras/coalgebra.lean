import ..functors.functor

universe w

namespace category_theory

-- structure coalgebra (C: category) [F : functor C C] :=
-- (A : C.C₀)
-- (ϕ : C.hom A (F.map_obj A))

structure coalgebra {C: category} (F : functor C C) :=
(A : C.C₀)
(ϕ : C.hom A (F.map_obj A))

-- structure coalgebra (C: category) :=
-- (A : C.C₀)
-- (F : functor C C)
-- (ϕ : C.hom A (F.map_obj A))


end category_theory

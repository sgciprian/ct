import category
import functors

open category_theory

-- Implementing the identity functor
-- This functor maps C to C, and changes nothing.

def Id (C : category) : functor C C :=
{
  map_obj := λ x, x,
  map_hom := λ x y f, f,
  comp := begin intros, trivial end,
  id := begin intros, trivial end
}

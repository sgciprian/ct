import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
namespace category_theory

def catamorphism {C : category} {F : functor C C} (A : initial (AlgebraCategory F)) (B : Falgebra F) :
  Fhomomorphism A.object B :=
A.exist_morph B

end category_theory
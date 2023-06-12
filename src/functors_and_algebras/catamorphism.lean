import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
namespace category_theory

-- A catamorphism is a unique morphism ∎ψ∎ 
-- from an initial F-Algebra to another F-algebra with morphism ψ : 𝔽 (Y) → Y
--              φ
--       𝔽(X)   →   X
--
--   F(∎ψ∎) ↓         ↓ ∎ψ∎
--
--       F(Y)   →   Y
--              ψ
def catamorphism {C : category} {F : functor C C} (A : initial (AlgebraCategory F)) (B : Falgebra F) :
  Fhomomorphism A.object B :=
A.exist_morph B

end category_theory
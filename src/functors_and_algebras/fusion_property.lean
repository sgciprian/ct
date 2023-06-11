import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
namespace category_theory

def fusion {ℂ : category} {F : functor ℂ ℂ} (A : initial (AlgebraCategory F)) (B C : Falgebra F) (f : ℂ.hom B.object C.object) 
(square_proof : ℂ.compose f B.function = ℂ.compose C.function (F.map_hom f)) : ℂ.compose f (A.exist_morph B).morph = (A.exist_morph C).morph :=
begin
  have h := A.is_unique ((AlgebraCategory F).compose {morph := f, square_proof:= square_proof} (A.exist_morph B)),
  cases (A.exist_morph C),
  cases h,
  simp [h],
end

end category_theory
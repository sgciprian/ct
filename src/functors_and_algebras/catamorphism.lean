import category
import functors
import functors_and_algebras.tools
import functors_and_algebras.algebra_category
import instances.Falgebras.initial_list_algebra
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

lemma catamorphic_recursion {C : category} {F : functor C C} (A : initial (AlgebraCategory F)) (B : Falgebra F) :
∀ (iso : isomorphism A.object.function) , ((A.exist_morph B).morph = C.compose B.function (C.compose (F.map_hom (A.exist_morph B).morph) iso.inverse)) :=
  begin
    intros,
    have h1 : C.compose B.function (C.compose (F.map_hom (A.exist_morph B).morph) iso.inverse) =
    C.compose (C.compose B.function  (F.map_hom (A.exist_morph B).morph)) iso.inverse := by simp [C.assoc],
    rw h1,
    simp [←(A.exist_morph B).square_proof],
    have h2 : C.compose (C.compose (A.exist_morph B).morph A.object.function) iso.inverse =
    C.compose  (A.exist_morph B).morph (C.compose A.object.function iso.inverse) := by simp [C.assoc],
    rw h2,
    have h3 : C.compose A.object.function iso.inverse = C.id A.object.object := by simp [iso.idl],
    rw h3,
    simp [C.left_id],
  end

def list_iso {A : Set.C₀} : isomorphism (initial_list_algebra_proof A).object.function := {
  inverse := 
  begin
    intro xs,
    cases xs,
    case List.nil {
      exact Either.left Singleton.star,
    },
    case List.cons : hd tl {
      exact Either.right ⟨hd, tl⟩,
    }, 
  end,
  idl :=
  begin
    simp,
    apply funext,
    intro xs,
    induction xs,
    case List.nil {
      refl,
    },
    case List.cons : hd tl ih {
      refl,
    },
  end,
  idr :=
  begin
    simp,
    apply funext,
    intro xs,
    cases xs,
    case Either.left : s {
      cases s,
      refl,
    },
    case Either.right : p {
      cases p,
      refl,
    },
  end,
}

lemma fold_eq {A : Set.C₀} {B : Falgebra (list_algebra_functor A)} : fold B.function = 
  Set.compose B.function (Set.compose ((list_algebra_functor A).map_hom (fold B.function)) list_iso.inverse) :=
  begin
    exact catamorphic_recursion (initial_list_algebra_proof A) B list_iso,
  end 

end category_theory
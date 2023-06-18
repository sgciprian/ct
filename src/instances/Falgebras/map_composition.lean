import instances.Set_category
import functors_and_algebras.tools
import instances.Falgebras.initial_list_algebra
import functors_and_algebras.fusion_property

open category_theory

-- Definition of map 
def map {A B : Set.C₀} (f : Set.hom A B) : Set.hom (List A) (List B) :=
  fold (List_fun (λ _, List.nil) (λ p, List.cons (f (fst p)) (snd p)))

def map_algebra {A B : Set.C₀} (f : Set.hom A B):
 Falgebra (list_algebra_functor A) :=
{
  object := List B,
  function := List_fun (λ _, List.nil) (λ p, List.cons (f (fst p)) (snd p))
}

def hom_map_alg {A B C: Set.C₀} (f : Set.hom A B) (g : Set.hom B C) : 
  Fhomomorphism (map_algebra f)  (map_algebra (Set.compose g f)) := {
    morph := map g,
    square_proof :=
    begin
      apply funext,
      intro l,
      cases l,
      case Either.left {
        refl,
      },
      case Either.right : p {
        refl,
      },
    end,
  }

def map_composition {A B C: Set.C₀} : ∀ (f : Set.hom A B) (g : Set.hom B C), 
  Set.compose (map g) (map f) = map (Set.compose g f) := 
  begin
    intros,
    have h1 := fusion (initial_list_algebra_proof A) (map_algebra f) (map_algebra (Set.compose g f)) (hom_map_alg f g).morph (hom_map_alg f g).square_proof,
    have h2 : (hom_map_alg f g).morph = map g := by refl,
    rw ←h2,
    have h3 : ((initial_list_algebra_proof A).exist_morph (map_algebra f)).morph = map f := by refl,
    rw ←h3,
    have h5 : ((initial_list_algebra_proof A).exist_morph (map_algebra (Set.compose g f))).morph = map (Set.compose g f) := by refl,  
    rw ←h5,
    rw h1,
  end 
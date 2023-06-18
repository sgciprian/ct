import instances.Set_category
import functors
import .tools

namespace category_theory

def bin_tree_algebra_functor (A : Set.C₀) : functor Set Set := {
  map_obj:= λ X, Either A (Pair X X),
  map_hom:= 
  begin
    intros X Y f x,
    cases x,
    case Either.left : l {
      exact Either.left l,
    },
    case Either.right : p {
      exact Either.right ⟨f (fst p), f (snd p)⟩
    },
  end,
  id:=
  begin
    intro,
    simp,
    apply funext,
    intro,
    cases x,
    case Either.left : l {
      refl,  
    },
    case Either.right : p {
      simp,
      have h1 : ⟨Set.id X (fst p),Set.id X (snd p)⟩ = ⟨fst p, snd p⟩ := by refl,
      rw h1,
      simp [pair_eq],
      refl,
    },
  end,
  comp:= 
  begin
    intros,
    simp,
    apply funext,
    intro,
    cases x,
    case Either.left : l {
      refl,
    },
    case Either.right : p {
      simp,
      have h1 : ⟨Set.compose g f (fst p),Set.compose g f (snd p)⟩ = ⟨g (f (fst p)), g (f (snd p))⟩ := by refl,
      rw h1,
      refl,
    },
  end,
}

end category_theory
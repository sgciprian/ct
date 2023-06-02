import instances.Set_category
import functors.functor
import .tools
namespace category_theory

-- F𝔸 functor : X → 1 + (𝔸 × X)
def ListFunctor (A : Set.C₀) : functor Set Set :=
{
  map_obj := λ X, Either Singleton (Pair A X),
  map_hom := 
  begin 
    intros x y f E,
    cases E,
    case Either.left : a {
      exact Either.left a
    },
    case Either.right : b {
      exact Either.right ⟨fst b, f (snd b)⟩
    }
  end,
  id :=
  begin
    intro _,
    simp,
    apply funext,
    intro x,
    cases x,
    case Either.left : a {
      simp,
      refl,
    },
    case Either.right : b {
      simp,
      have h : ⟨fst b,Set.id X (snd b)⟩ 
        = ⟨fst b, snd b⟩ := by refl,
      rw h,
      simp [pair_eq b],
      refl
    }
  end,
  comp:= 
  begin
    intros _ _ _ f g,
    simp,
    apply funext,
    intro x,
    cases x,
    case Either.left : a {
      simp,
      refl
    },
    case Either.right : b {
      simp,
      have h : ⟨fst b, Set.compose g f (snd b)⟩ 
        = ⟨fst b, g (f (snd b))⟩ := by refl,
      rw h,
      refl
    }
  end
}

end category_theory
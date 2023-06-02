import instances.Set_category
import functors
import .tools

namespace category_theory

-- F functor : X → 1 + X
def MaybeFunctor : functor Set Set :=
{
  map_obj := λ X, Either Singleton X,
  map_hom := 
  begin 
    intros x y f E,
    cases E,
    case Either.left : a {
      exact Either.left a
    },
    case Either.right : b {
      exact Either.right (f b)
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
      refl
    }
  end
}

end category_theory
import instances.Set_category
import functors.functor

open category_theory

inductive Maybe (α : Type)
  | none : Maybe
  | some : α → Maybe

-- Example of the Maybe functor 
-- as known from Functional Programming Languages
def MaybeFunctor : functor Set Set :=
{
  map_obj := λ A, Maybe A,
  map_hom :=
  begin
    intros α β f as,
    induction as,
    case Maybe.none {
      exact Maybe.none
    },
    case Maybe.some : x {
      exact Maybe.some (f x)
    }
  end,
  comp :=
  begin
    intros _ _ _ f g,
    simp,
    apply funext,
    intro xs,
    induction xs,
    case Maybe.none {
      simp,
      refl
    },
    case Maybe.some : x {
      simp,
      refl
    }
  end,
  id :=
  begin
    intros _,
    simp,
    apply funext,
    intro xs,
    induction xs,
    case Maybe.none {
      simp,
      refl
    },
    case Maybe.some : x {
      simp,
      refl
    }
  end
}
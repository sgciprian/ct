import instances.Set_category
import functors.functor

open category_theory

inductive List (α: Type) : Type
  | nil : List
  | cons (head: α) (tail: List) : List


-- Example of the List functor 
-- as known from Functional Programming Languages
def ListFunctor : functor Set Set :=
{
  map_obj := λ A, List A,
  map_hom :=
  begin
    intros α β f as,
    induction as,
    case List.nil {
      exact List.nil
    },
    case List.cons : x xs ih {
      exact List.cons (f x) ih
    }
  end,
  comp :=
  begin
    intros _ _ _ f g,
    simp,
    apply funext,
    intro xs,
    induction xs,
    case List.nil {
      simp,
      refl
    },
    case List.cons : x xs ih {
      simp,
      rw ih,
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
    case List.nil {
      simp,
      refl
    },
    case List.cons : x xs ih {
      simp,
      rw ih,
      refl
    }
  end
}
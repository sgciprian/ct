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
  -- Objects are mapped to Lists 
  map_obj := λ A, List A,
  -- Morphisms are mapped using induction over the input List
  -- In the base case we return Nil, and when mapping Cons (head, tail)
  -- we apply the given function to the head element and recursively continue with the tail. 
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
  -- Induction is used to prove that composition is preserved
  -- Here, the base case still returns Nil.
  -- Given Cons(head, tail) lean is smart and understands that 
  -- we would apply the composition of g and f to the head element, followed by
  -- a recursive operation on the tail. Thus we have a clean and concise proof.
  comp :=
  begin
    intros _ _ _ f g,
    simp,
    apply funext,
    intro xs,
    induction xs,
    case List.nil {
      simp,
      refl,
    },
    case List.cons : x xs ih {
      simp,
      rw ih,
      refl,
    }
  end,
  -- The identity is preserved as applying C.id to each element inside the list
  -- applies no changes to the list, which is the same as applying it to the List from the "outside".
  -- A proof by induction is used again. As for the composition, Lean helps us write a concise proof.
  id :=
  begin
    intros _,
    simp,
    apply funext,
    intro xs,
    induction xs,
    case List.nil {
      simp,
      refl,
    },
    case List.cons : x xs ih {
      simp,
      rw ih,
      refl,
    }
  end
}
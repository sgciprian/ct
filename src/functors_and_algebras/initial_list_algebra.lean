import category
import instances.Set_category
import instances.functors.List_functor
import functors_and_algebras.tools
import functors_and_algebras.f_algebra
import functors_and_algebras.list_functor
import functors_and_algebras.algebra_category

namespace category_theory

-- Morphism 𝔽 (X) → X
def List_fun {A X : Set.C₀} (n : Singleton → X) (c : Pair A X → X) 
: Set.hom ((list_algebra_functor A).map_obj X) X :=
  begin
    have test : Either Singleton (Pair A X) = (list_algebra_functor A).map_obj X := by refl,
    rw ←test,
    intro x,
    cases x,
    { exact n x },
    { exact c x }
  end

def init_list (A : Set.C₀) : (AlgebraCategory (list_algebra_functor A)).C₀ := {
  object := List A,
  function := List_fun (λ _, List.nil) (λ x, List.cons (fst x) (snd x))
}


def fold {A B : Set.C₀} : (Set.hom ((list_algebra_functor A).map_obj B) B) → Set.hom (List A) B :=
begin
  have test : (list_algebra_functor A).map_obj B = Either Singleton (Pair A B) := by refl,
  rw test,
  intros f x,
  induction x,
  case List.nil {
    exact f (Either.left Singleton.star)
  },
  case List.cons : hd _ ih {
    exact f (Either.right ⟨hd, ih⟩)
  }
end

def init_hom  {S : Set.C₀} (B : Falgebra (list_algebra_functor S)) : Fhomomorphism (init_list S) B := 
{
  morph := fold B.function,
  square_proof := 
  begin
    apply funext,
    intro l,
    have h : Set.compose (fold B.function) (init_list S).function l 
    = fold B.function ((init_list S).function l) := by refl,
    
    rw h,

    have h1 : Set.compose B.function ((list_algebra_functor S).map_hom (fold B.function)) l =
    B.function (((list_algebra_functor S).map_hom (fold B.function)) l) 
     := by refl,
    rw h1,
    
    cases l,
    case Either.left : s {
      have h2 : fold B.function ((init_list S).function (Either.left s))
      = fold B.function (List.nil) := by refl,
      have h3 : fold B.function (List.nil) = B.function (Either.left Singleton.star)
      := by refl,
      rw [h2, h3],
      have h4 : B.function (((list_algebra_functor S).map_hom (fold B.function)) (Either.left s))
      = B.function (Either.left s) := by refl,
      rw h4,
      have test : s = Singleton.star :=
        begin 
          cases s,
          refl,
        end,
      rw test,
    },
    case Either.right : p {
      have h2 : fold B.function ((init_list S).function (Either.right p))
      = fold B.function (List.cons (fst p) (snd p)) := by refl,

      have h3 : fold B.function (List.cons (fst p) (snd p))
       = B.function (Either.right ⟨(fst p), (fold B.function (snd p))⟩)
      := by refl,
      rw [h2, h3],

      have h4 : B.function (((list_algebra_functor S).map_hom (fold B.function)) (Either.right p))
      = B.function (Either.right ⟨(fst p), (fold B.function (snd p))⟩) := by refl,
      rw h4,
    },
  end,
} 

def initial_list_algebra {A : Set.C₀} : initial ((AlgebraCategory (list_algebra_functor A))) := 
{
  object := init_list A,
  exist_morph := init_hom, 
  is_unique := 
    begin
      intros X f,
      simp [init_hom],
      cases f,
      have test : f_morph = fold X.function :=
        begin
          apply funext,
          intro x,
          induction x,
          case List.nil {
            have temp1 : fold X.function List.nil = X.function (Either.left Singleton.star) := by refl,
            simp [temp1],
            have temp2 : f_morph List.nil = f_morph ((init_list A).function (Either.left Singleton.star)) := by refl,
            simp [temp2],
            have temp3 : f_morph ((init_list A).function (Either.left Singleton.star)) = (Set.compose f_morph (init_list A).function) (Either.left Singleton.star) := by refl,
            simp [temp3],
            have temp4 : (Set.compose f_morph (init_list A).function) (Either.left Singleton.star) = (Set.compose X.function ((list_algebra_functor A).map_hom f_morph)) (Either.left Singleton.star) := by simp [f_square_proof],
            simp [temp4],
            have temp5 : Set.compose X.function ((list_algebra_functor A).map_hom f_morph) (Either.left ⋆) = X.function (((list_algebra_functor A).map_hom f_morph) (Either.left ⋆)) := by refl,
            simp [temp5],
            have temp6 : (list_algebra_functor A).map_hom f_morph (Either.left Singleton.star) = Either.left Singleton.star := by refl,
            simp [temp6]
          },
          case List.cons : hd tl ih {
            have temp1 : fold X.function (List.cons hd tl) = Set.compose X.function ((list_algebra_functor A).map_hom (fold X.function)) (Either.right ⟨hd, tl⟩) := by refl,
            simp [temp1],
            have temp2 : f_morph (List.cons hd tl) = Set.compose f_morph (init_list A).function (Either.right ⟨hd, tl⟩) := by refl,
            simp [temp2],
            have temp3 : Set.compose f_morph (init_list A).function (Either.right ⟨hd, tl⟩) = Set.compose X.function ((list_algebra_functor A).map_hom f_morph) (Either.right ⟨hd, tl⟩) := by simp [f_square_proof],
            simp [temp3],
            have temp4 : Set.compose X.function ((list_algebra_functor A).map_hom (fold X.function)) (Either.right ⟨hd, tl⟩) = X.function (((list_algebra_functor A).map_hom (fold X.function)) (Either.right ⟨hd, tl⟩)) := by refl,
            simp [temp4],
            have temp5 : (list_algebra_functor A).map_hom (fold X.function) (Either.right ⟨hd, tl⟩) = Either.right ⟨hd, fold X.function tl⟩ := by refl,
            simp [temp5],
            simp [←ih],
            refl
          }
        end,
      simp [test]
    end
}

end category_theory
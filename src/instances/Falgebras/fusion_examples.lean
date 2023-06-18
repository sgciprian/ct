import instances.Set_category
import functors_and_algebras.tools
import .initial_list_algebra
import functors_and_algebras.list_functor
import functors_and_algebras.fusion_property

open category_theory

def list_algebra (A : Set.C₀) (f : (Set.hom ((list_algebra_functor A).map_obj (List A)) (List A))) :
 Falgebra (list_algebra_functor A) :=
{
  object := List A,
  function := f
}

def map_algebra (A B : Set.C₀) (f : (Set.hom ((list_algebra_functor A).map_obj (Set.hom (List A) (List B))) (Set.hom (List A) (List B)))) :
 Falgebra (list_algebra_functor A) :=
{
  object := Set.hom (List A) (List B),
  function := f
}

def filter {A : Set.C₀} : (A → bool)→ (List A) → (List A)
  | f List.nil := List.nil
  | f (List.cons hd tl) := if (f hd) then List.cons hd (filter f tl) else filter f tl

def filter_as_fold {A : Set.C₀} (f : A → bool) : Set.hom (List A) (List A) :=
  fold (List_fun (λ _, List.nil) (λ p, if (f (fst p)) then List.cons (fst p) (snd p) else (snd p)))

def length {A : Set.C₀} : (List A) → nat 
  | List.nil := nat.zero
  | (List.cons hd tl) := nat.succ (length tl)

def length_as_fold {A : Set.C₀} : Set.hom (List A) nat :=
  fold (List_fun (λ _, nat.zero) (λ p, nat.succ (snd p)))

lemma fold_eq_length : ∀ {A : Set.C₀} (l : List A), length l = length_as_fold l :=
begin
  intros A l,
  induction l,
  case List.nil {
    refl,
  },
  case List.cons : hd tl ih {
    have h1 : length (List.cons hd tl) = nat.succ (length tl) := by refl,
    have h2 : length_as_fold (List.cons hd tl) = nat.succ (length_as_fold tl) := by refl,
    rw [h1,h2,ih],
  },
end

lemma fold_eq_filter : 
  ∀ {A : Set.C₀} (f : A → bool) (l : List A), filter f l = filter_as_fold f l := 
begin
  intros A f l,
  induction l,
  case List.nil {
    refl,
  },
  case List.cons : hd tl ih {
    have h1 : filter f (List.cons hd tl) = 
      if (f hd) then List.cons hd (filter f tl) else filter f tl := by refl,
    have h2 : filter_as_fold f (List.cons hd tl) = 
      if (f hd) then List.cons hd (filter_as_fold f tl) else filter_as_fold f tl := by refl,
    rw [h1,h2,ih],
  },
end

def alg_length {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := ℕ,
  function := List_fun (λ _, nat.zero) (λ p, nat.succ (snd p)),
}

def alg_filter {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := List A,
  function := (List_fun (λ _, List.nil) (λ p, if (f (fst p)) then List.cons (fst p) (snd p) else (snd p))),
}

def alg_length_filtered {A : Set.C₀} (f : A → bool) : Falgebra (list_algebra_functor A) := {
  object := ℕ,
  function := List_fun (λ _, nat.zero) (λ p, if (f (fst p)) then nat.succ (snd p) else (snd p)),
}


def hom_f_l {A : Set.C₀} (f : A→ bool) : Fhomomorphism (alg_filter f) (alg_length_filtered f) := {
  morph := length_as_fold,
  square_proof := 
  begin
    apply funext,
    intro x,
    cases x,
    case Either.left {
      refl,
    },
    case Either.right : p {
      have h1 : Set.compose (alg_length_filtered f).function ((list_algebra_functor A).map_hom length_as_fold) (Either.right p) =
      (alg_length_filtered f).function (((list_algebra_functor A).map_hom length_as_fold) (Either.right p)) := by refl,
      rw h1,
      have h2 : ((list_algebra_functor A).map_hom length_as_fold) (Either.right p) = 
        Either.right ⟨fst p, length_as_fold (snd p)⟩ := by refl,
      rw h2,
      have h3 : Set.compose length_as_fold (alg_filter f).function (Either.right p) = 
      length_as_fold ((alg_filter f).function (Either.right p)) := by refl,
      rw h3,
      have h4 : (alg_filter f).function (Either.right p) = (λ x, if (f (fst x)) then List.cons (fst x) (snd x) else snd x) p := by refl,
      rw h4,
      have h5 : (alg_length_filtered f).function (Either.right ⟨fst p,length_as_fold (snd p)⟩) = 
      if (f (fst ⟨fst p,length_as_fold (snd p)⟩)) 
      then nat.succ (snd ⟨fst p,length_as_fold (snd p)⟩) else snd ⟨fst p,length_as_fold (snd p)⟩:= by refl,
      rw h5,
      have h7 : ((λ (x : Pair A (List A)), ite ↥(f (fst x)) (List.cons (fst x) (snd x)) (snd x)) p) =
        ite ↥(f (fst p)) (List.cons (fst p) (snd p)) (snd p) := by refl,
      rw h7,

      cases (f (fst p)),
      case bool.ff {
        have h6 : ite ↥ff (snd ⟨fst p,length_as_fold (snd p)⟩).succ (snd ⟨fst p,length_as_fold (snd p)⟩) =
        length_as_fold (snd p) := by refl,
        rw h6,
        have h7 : (ite ↥ff (List.cons (fst p) (snd p)) (snd p)) = snd p := by refl,
        rw h7,
      },
      case bool.tt {
        have h6 : (ite ↥tt (List.cons (fst p) (snd p)) (snd p)) = List.cons (fst p) (snd p) := by refl,
        rw h6,
        have h7 : ite ↥tt (snd ⟨fst p,length_as_fold (snd p)⟩).succ (snd ⟨fst p,length_as_fold (snd p)⟩) =
          nat.succ (length_as_fold (snd p)) := by refl,
        rw h7,
        have h8 : length_as_fold (List.cons (fst p) (snd p)) =  nat.succ (length_as_fold (snd p)) := by refl,
        rw h8,
      },
    },
  end,
}

def eq_length_comp_filter_cat : ∀ {A : Set.C₀} (f : A → bool), Set.compose length (filter f) = fold (alg_length_filtered f).function :=
begin
  intros A f,
  have h := fusion (initial_list_algebra_proof A) (alg_filter f) (alg_length_filtered f) (hom_f_l f).morph (hom_f_l f).square_proof,
  apply funext,
  intro l,
  have h1 : Set.compose length (filter f) l = length ((filter f) l) := by refl,
  rw h1,
  rw [fold_eq_filter f l],
  rw [fold_eq_length (filter_as_fold f l)],
  have h2 : length_as_fold ((filter_as_fold f) l) = Set.compose length_as_fold (filter_as_fold f) l := by refl,
  rw h2,
  have h3 : (hom_f_l f).morph = length_as_fold := by refl,
  rw ←h3,
  have h4 : ((initial_list_algebra_proof A).exist_morph (alg_filter f)).morph = filter_as_fold f := by refl,
  rw ←h4,
  have h5 : fold (alg_length_filtered f).function = ((initial_list_algebra_proof A).exist_morph (alg_length_filtered f)).morph := by refl,
  rw h5,
  simp [h],
end
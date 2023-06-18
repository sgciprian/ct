import instances.Set_category
import functors_and_algebras.bin_tree_functor
import functors_and_algebras.f_algebra
import functors_and_algebras.tools
import functors_and_algebras.algebra_category

open category_theory
open category_theory.BTree

def bin_tree_algebra {A : Set.C₀} : Falgebra (bin_tree_algebra_functor A) := {
  object := BTree A,
  function := 
  begin
    intro F,
    cases F,
    case Either.left : a {
      exact leaf a,
    },
    case Either.right : p {
      exact node (fst p) (snd p),
    },
  end,
}

def bin_tree_hom {A : Set.C₀} (to : Falgebra (bin_tree_algebra_functor A)) : Fhomomorphism bin_tree_algebra to := {
  morph:= 
      begin
        intro x,
        induction x,
        case leaf : a {
          exact to.function (Either.left a),
        },
        case node : l r ihl ihr {
          exact to.function (Either.right ⟨ihl, ihr⟩),
        },
      end,
      square_proof:= 
      begin
        simp,
        apply funext,
        intro x,
        cases x,
        case Either.left : a {
          refl,
        },
        case Either.right : p {
          refl,
        },
      end,
}

def bin_tree_algebra_initial_proof {A : Set.C₀} : initial (AlgebraCategory (bin_tree_algebra_functor A)) := {
  object := bin_tree_algebra,
  exist_morph:=
  begin
    intros to,
    exact bin_tree_hom to,
  end,
  is_unique:=
  begin
    intros,
    cases f,
    have h : f_morph = (bin_tree_hom X).morph := 
    begin
      apply funext,
      intro x,
      induction x,
      case leaf : a {
        have h1 : leaf a = bin_tree_algebra.function (Either.left a) := by refl,
        rw h1,
        have h2 : f_morph (bin_tree_algebra.function (Either.left a)) = 
        Set.compose f_morph bin_tree_algebra.function (Either.left a) := by refl,
        rw h2,
        rw f_square_proof,
        have h3 : (bin_tree_hom X).morph (bin_tree_algebra.function (Either.left a)) = 
        Set.compose (bin_tree_hom X).morph bin_tree_algebra.function (Either.left a) := by refl,
        rw h3,
        rw (bin_tree_hom X).square_proof,
        refl,
      },
      case node : l r lih rih {
        have h1 : (bin_tree_hom X).morph (node l r) 
        = X.function (Either.right ⟨(bin_tree_hom X).morph l, (bin_tree_hom X).morph r⟩):= by refl, 
        rw h1,
        rw [←lih, ←rih],
        have h2 : node l r = bin_tree_algebra.function (Either.right ⟨l, r⟩) := by refl,
        rw h2,
        have h3 : f_morph (bin_tree_algebra.function (Either.right ⟨l,r⟩)) = 
        Set.compose f_morph bin_tree_algebra.function (Either.right ⟨l,r⟩) := by refl,
        rw h3,
        rw f_square_proof,
        refl,
      }, 
    end,
    cases bin_tree_hom X,
    simp [h],
  end,
}
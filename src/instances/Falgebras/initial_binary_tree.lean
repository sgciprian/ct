import instances.Set_category
import functors_and_algebras.bin_tree_functor
import functors_and_algebras.f_algebra
import functors_and_algebras.tools
import functors_and_algebras.algebra_category

open category_theory
open category_theory.BTree

-- The algebra of the 𝔸 + (X × X) functor, where the object is a binary tree.
def bin_tree_algebra {A : Set.C₀} : Falgebra (bin_tree_algebra_functor A) := {
  -- The object is a binary tree.
  object := BTree A,
  -- Mapping 𝔸 + (X × X) to a Binary tree is done by:
  -- 1) 𝔸 is mapped to leaf (𝔸)
  -- 2) (X × X) is mapped to node X X, we can imagine the 2 elements of the product
  -- as the branches of a tree node.  
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

-- Construction of the universal homomorphism from the Algebra with object binary tree, to any algebra of the 𝔸 + (X × X) endofunctor
def bin_tree_hom {A : Set.C₀} (to : Falgebra (bin_tree_algebra_functor A)) : Fhomomorphism bin_tree_algebra to := {
  -- The morphism utilized the function of the other algebra, since this is a catamorphism.
  -- We can map the binary tree structure back to the form 𝔸 + (X × X) in order to have a compatible type.
  morph:= 
    begin
      intro x,
      induction x,
      case leaf : a {
        exact to.function (Either.left a),
      },
      -- Induction is used since, binary tree uses a recursive definition.
      case node : l r ihl ihr {
        exact to.function (Either.right ⟨ihl, ihr⟩),
      },
    end,
  -- Now we need to prove that the morphism commutes the diagram :
  --                    φ
  --      𝔸 + (X × X)   →   X
  --
  --   F(∎ψ∎) ↓             ↓ ∎ψ∎
  --
  --      𝔸 + (Y × Y)   →   Y
  --                    ψ
  -- This is a simple proof, since we know how the morphism utilizes ψ.
  -- Lean is able to alleviate the work on this proof, because The Set category utilizes 
  -- built-in features and we have defined the morphism directly during construction of the homomorphism,
  -- so Lean can automate the proof. 
  -- For a more detailed explanation, one can inspect the proof of why fold is a catamorphism for the categoty of algebras, defined by the 1 + (𝔸 × X) functor.
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
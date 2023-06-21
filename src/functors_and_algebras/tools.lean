import category
import functors.functor
import functors_and_algebras.f_algebra
import functors_and_algebras.algebra_category
namespace category_theory

universes u v

-- α + β
inductive Either (α : Type u) (β : Type v)
  | left : α → Either
  | right : β → Either

-- α ⨯ β
inductive Pair (α : Type u) (β : Type v)
  | pair : α → β → Pair

-- The singleton type
inductive Singleton
  | star : Singleton


notation `⟨` lhs `,` rhs `⟩` := Pair.pair lhs rhs
notation `⋆` := Singleton.star

def fst {α : Type u} {β : Type v} : Pair α β → α
| ⟨x, _⟩ := x

def snd {α : Type u} {β : Type v} : Pair α β → β
| ⟨_, y⟩ := y

-- Proof that a pair P is equal to a pair constructed using the first and second element of P
lemma pair_eq {α : Type u} {β : Type v}
  : ∀P : Pair α β, ⟨fst P, snd P⟩ = P
| ⟨x, y⟩ :=
  begin
    simp [fst, snd]
  end

-- I have redefined the initial object structure, since the one in universal_properties, is not correct.
structure initial (C : category) := 
  (object : C.C₀)
  (exist_morph : Π (X : C.C₀), C.hom object X)
  (is_unique : ∀ {X : C.C₀} (f : C.hom object X), f = exist_morph X)

structure initial_algebra {C : category} (F : functor C C) :=
  (alg : Falgebra F)
  (cata : ∀ {B : Falgebra F} (φ : C.hom (F.map_obj B.object) B.object), (AlgebraCategory F).hom alg B)
  (is_unique :  ∀ {X : (AlgebraCategory F).C₀} (f : (AlgebraCategory F).hom alg X), f = cata X.function)


def eq_r : ∀ {C : category} {F : functor C C} (A : initial_algebra F), initial (AlgebraCategory F) :=
begin
  intros,
  exact {
    object := A.alg,
    exist_morph := 
    begin
      intros,
      exact A.cata X.function,
    end,
    is_unique := 
    begin
      intros,
      exact A.is_unique f,
    end,
  }
end

def eq_l : ∀  {C : category} {F : functor C C} (A : initial (AlgebraCategory F)), initial_algebra F :=
begin
  intros,
  exact  {
    alg := A.object,
    cata := 
    begin
      intros,
      exact A.exist_morph B,
    end,
    is_unique :=
    begin
      intros,
      exact A.is_unique f,
    end,
  }
end
-- variable C : category
-- variable F : functor C C
-- #check initial_algebra F
-- #check initial (AlgebraCategory F)

-- theorem algrebra_initiality {C : category} {F : functor C C} : initial_algebra F = initial (AlgebraCategory F) :=
-- begin 

--   -- apply eq.congr,
--   -- apply classical.by_contradiction,
--   -- intro h,
--   -- cases h,

--   sorry,
--   -- have h1 := @eq_l C F,
--   -- have h2 := @eq_r C F,
--   -- have h3 := eq.to_iff ((initial_algebra F) = initial (AlgebraCategory F)),
  
--   -- rw [eq_l, eq_r],
-- end

class isomorphism {C : category} {N M : C.C₀} (hom : C.hom N M) :=
  (inverse : C.hom M N)
  (idl : C.compose hom inverse = C.id M)
  (idr : C.compose inverse hom = C.id N)


inductive List (α: Type) : Type
  | nil : List
  | cons (head: α) (tail: List) : List

inductive Maybe (α : Type)
  | none : Maybe
  | some : α → Maybe

inductive BTree (α : Type)
  | leaf (el : α) : BTree
  | node (l :BTree) (r : BTree) : BTree

end category_theory
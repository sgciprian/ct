import category
import functors

namespace category_theory 

structure natural_transformation {C D : category} (F G : functor C D) :=
  (α : Π (X : C.C₀) , D.hom (F.map_obj X) (G.map_obj X))
  (naturality_condition : ∀ {X Y : C.C₀} (f : C.hom X Y), 
    D.compose (G.map_hom f) (α X)  = 
    D.compose (α Y) (F.map_hom f)
  )

  -- notation
  infixr `==>`:90 := natural_transformation

  def bimap {C D E : category} {F F' : D => E} {G G' : C => D} (α : F ==> F') (β : G ==> G')
    : (F ⬝ G) ==> (F' ⬝ G') := sorry

  infixr (name := bimap) `×`:95 := bimap

  def nt_composition
    {C D : category}
    {F G H : C => D}
    (τ₁ : G ==> H) (τ₂ : F ==> G) : F ==> H :=
    {
      α := begin
        intros,
        let f := τ₁.α X,
        let g := τ₂.α X,
        let h := D.compose f g,
        exact h,
      end,
      naturality_condition := begin
        intros,
        let a := τ₁.naturality_condition f,
        let b := τ₂.naturality_condition f,
        rw D.assoc,
        rw a,
        rw ←D.assoc,
        rw b,
        rw D.assoc,
      end,
    }


end category_theory

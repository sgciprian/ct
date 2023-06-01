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

  def bimap {C D E : category} {F F' : C => D} {G G' : D => E} (β : G ==> G') (α : F ==> F')
    : (G ⬝ F) ==> (G' ⬝ F') :=
    {
      α := λ X, E.compose (β.α (F'.map_obj X)) (G.map_hom (α.α X)),
        -- A more verbose version:
        -- This was not chosen as it makes the liveview types unreadable.
        --  begin
        --    intros,
        --    let f := α.α X,
        --    let F'X := F'.map_obj X,
        --    let Gf := G.map_hom f,
        --    let g := β.α F'X,
        --    let comp := E.compose g Gf,
        --    exact comp,
        --  end,
      naturality_condition := begin
        intros,
        let sq1 := α.naturality_condition f,
        let gsq : E.compose (G.map_hom (F'.map_hom f)) (G.map_hom (α.α X)) = 
                  E.compose (G.map_hom (α.α Y)) (G.map_hom (F.map_hom f)) := begin
          rw ←G.comp,
          symmetry,
          rw ←G.comp,
          rw ←keep_equation,
          exact sq1,
        end,
        let sq2 := β.naturality_condition (F'.map_hom f),
        let map_eq : (G' ⬝ F').map_hom f = G'.map_hom (F'.map_hom f) := begin
          intros,
          trivial,
        end,
        let map_eq2 : G.map_hom (F.map_hom f) = (G ⬝ F).map_hom f := begin
          intros,
          trivial,
        end,
        rw E.assoc,
        rw map_eq,
        rw sq2,
        rw ←E.assoc,
        rw gsq,
        rw E.assoc,
        rw map_eq2,
      end
    }

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

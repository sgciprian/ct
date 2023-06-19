import category
import functors
import natural_transformation.definition

namespace category_theory

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
      α := λ X, D.compose (τ₁.α X) (τ₂.α X),
 --      begin
 --        intros,
 --        let f := τ₁.α X,
 --        let g := τ₂.α X,
 --        let h := D.compose f g,
 --        exact h,
 --      end,
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

  infixr (name := nt_composition) `⊚`:90 := nt_composition

  def ID {C D : category} (F : C => D) : F ==> F :=
    {
      α := λ X, D.id (F.map_obj X),
      naturality_condition := begin
        intros,
        rw D.left_id,
        rw D.right_id,
      end,
    }

end category_theory

import morphisms
import functors.composition
import natural_transformation.definition
import natural_transformation.composition

namespace category_theory

  def is_iso_nt {C D : category} {F G : C => D} (α : F ==> G) :=
    Π X : C.C₀, is_iso (α.α X)

  def assoc_nt {B C D E : category} (F : B => C) (G : C => D) (H : D => E)
    : H ⬝ (G ⬝ F) ==> (H ⬝ G) ⬝ F :=
    {
      α := λ X, H.map_hom (G.map_hom (F.map_hom (B.id X))),
      naturality_condition := begin
        intros,
        rw [F.id, G.id],
        rw H.id (G.map_obj (F.map_obj X)),
        change E.compose (H.map_hom (G.map_hom (F.map_hom f))) (E.id (H.map_obj (G.map_obj (F.map_obj X)))) = E.compose (H.map_hom (G.map_hom (F.map_hom (B.id Y)))) ((H ⬝ G ⬝ F).map_hom f),
        rw E.left_id,
        symmetry,
        rw [F.id, G.id, H.id],
        change E.compose (E.id (H.map_obj (G.map_obj (F.map_obj Y)))) (H.map_hom (G.map_hom (F.map_hom f))) = H.map_hom (G.map_hom (F.map_hom f)),
        rw E.right_id,
      end
    }

  theorem assoc_nt_iso {B C D E : category} {F : B => C} {G : C => D} {H : D => E}
    : is_iso_nt (assoc_nt F G H) :=
    begin
      intros,
      rw is_iso_nt,
      intros,
      rw is_iso,
      change
        ∃ (g : E.hom (H.map_obj (G.map_obj (F.map_obj X))) (H.map_obj (G.map_obj (F.map_obj X)))),
          E.compose g ((assoc_nt F G H).α X) = E.id (H.map_obj (G.map_obj (F.map_obj X))) ∧
          E.compose ((assoc_nt F G H).α X) g = E.id (H.map_obj (G.map_obj (F.map_obj X))),
      existsi E.id (H.map_obj (G.map_obj (F.map_obj X))),
      split,
      rw E.right_id,
      rw assoc_nt,
      change H.map_hom (G.map_hom (F.map_hom (B.id X))) = E.id (H.map_obj (G.map_obj (F.map_obj X))),
      rw [F.id, G.id, H.id],
      rw E.left_id,
      rw assoc_nt,
      change H.map_hom (G.map_hom (F.map_hom (B.id X))) = E.id (H.map_obj (G.map_obj (F.map_obj X))),
      rw [F.id, G.id, H.id],
      done,
    end

  def left_unit_nt {C D : category} (F : C => D)
    : Id D ⬝ F ==> F :=
    {
      α := λ X, F.map_hom $ C.id X,
      naturality_condition := begin
        intros,
        rw ←F.comp,
        rw C.left_id,
        rw ←(D.right_id $ F.map_hom f),
        rw ←F.id,
        trivial,
      end
    }

  theorem left_unit_nt_iso {C D : category} (F : C => D)
    : is_iso_nt $ left_unit_nt F :=
    begin
      intros,
      rw is_iso_nt,
      admit,
    end

  def right_unit_nt {C D : category} (F : C => D)
    : F ⬝ Id C ==> F :=
    {
      α := sorry,
      naturality_condition := begin
        intros,
        admit,
      end
    }

  theorem right_unit_nt_iso {C D : category} (F : C => D)
    : is_iso_nt $ right_unit_nt F :=
    begin
      intros,
      rw is_iso_nt,
      admit,
    end

end category_theory

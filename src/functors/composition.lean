import functors.functor

namespace category_theory

  -- Creates the composition of two functors.
  def composition_functor {C D E : category} (G : functor D E) (F : functor C D) : functor C E :=
  {
    map_obj := λ X : C, G.map_obj (F.map_obj X),
    map_hom := λ X Y : C, λ f, G.map_hom (F.map_hom f),
    id :=
      begin
        intro,
        rw F.id,
        rw G.id,
      end,
    comp :=
      begin
        intros,
        rw F.comp,
        rw G.comp,
      end,
  }
  -- notation
  infixr `⬝`:90 := composition_functor

  def functor_comp_assoc {B C D E : category} : ∀ (F : B => C) (G : C => D) (H : D => E),
    (H ⬝ G) ⬝ F = H ⬝ (G ⬝ F) := begin
      intros,
      trivial,
    end

end category_theory

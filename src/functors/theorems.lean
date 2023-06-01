import functors.functor
import category

namespace category_theory

  theorem keep_equation {C D : category} (F : C => D) :
    ∀ {X Y : C.C₀} (f g : C.hom X Y), f = g → F.map_hom f = F.map_hom g :=
  begin
    intros X Y f g heq,
    rw heq,
  end

end category_theory

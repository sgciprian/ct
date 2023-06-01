import category.category

namespace category_theory

  theorem double_square 
    {C : category}
    {X Y Z P Q R : C.C₀}
    {a : C.hom X Y}
    {b : C.hom Y Z}
    {c : C.hom P Q}
    {d : C.hom Q R}
    {e : C.hom X P}
    {f : C.hom Y Q}
    {g : C.hom Z R}
    :
    (C.compose g b = C.compose d f) ∧
    (C.compose f a = C.compose c e) →
    (C.compose (C.compose g b) a) = (C.compose d (C.compose c e))
    :=
    begin
      intros sq,
      cases sq with sq1 sq2,
      rw sq1,
      rw ←sq2,
      rw C.assoc,
    end

  theorem extend
    {C : category}
    {X Y Z : C.C₀}
    {f g : C.hom X Y}
    (h : C.hom Y Z)
    :
    f = g → C.compose h f = C.compose h g
    :=
    begin
      intros a,
      rw a,
    end

end category_theory

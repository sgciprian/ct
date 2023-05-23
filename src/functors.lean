import .category

namespace category_theory

structure functor :=
  (C : category)
  (D : category)
  (map_obj : C.C₀ → D.C₀)
  (map_hom : Π {X Y : C.C₀} (f : C.hom X Y), D.hom (map_obj X) (map_obj Y))
  (id : ∀ (X : C.C₀), map_hom (C.id X) = D.id (map_obj X))
  (comp : ∀ {X Y Z : C.C₀} (f : C.hom X Y) (g : C.hom Y Z), map_hom (C.compose g f) = D.compose (map_hom g) (map_hom f))

def functor_map (F: functor) {X Y : F.C.C₀} (f : F.C.hom X Y) :  F.D.hom (F.map_obj X) (F.map_obj Y) := F.map_hom f

class full {F: functor} :=
  (full : ∀ {X Y : F.C.C₀} (g : F.D.hom (F.map_obj X) (F.map_obj Y)), ∃ (f : F.C.hom X Y), (F.map_hom f) = g)

class faithful {F: functor} :=
  (faithful : ∀ {X Y : F.C.C₀} {f g : F.C.hom X Y} (h : functor_map F f = functor_map F g), f = g)

end category_theory
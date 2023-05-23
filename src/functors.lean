import .category

namespace category_theory

structure functor (C D : category) :=
  (map_obj : C → D)
  (map_hom : Π {X Y : C} (f : C.hom X Y), D.hom (map_obj X) (map_obj Y))
  (id : ∀ (X : C), map_hom (C.id X) = D.id (map_obj X))
  (comp : ∀ {X Y Z : C} (f : C.hom X Y) (g : C.hom Y Z), map_hom (C.compose g f) = D.compose (map_hom g) (map_hom f))

def functor_map {C D : category} (F: functor C D) {X Y : C} (f : C.hom X Y) :  D.hom (F.map_obj X) (F.map_obj Y) := F.map_hom f

class full {C D : category} {F: functor C D} :=
  (full : ∀ {X Y : C} (g : D.hom (F.map_obj X) (F.map_obj Y)), ∃ (f : C.hom X Y), (F.map_hom f) = g)

class faithful {C D : category} {F: functor C D} :=
  (faithful : ∀ {X Y : C} {f g : C.hom X Y} (h : functor_map F f = functor_map F g), f = g)

end category_theory
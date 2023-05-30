import category

namespace category_theory

structure functor (C D : category) :=
  (map_obj : C → D)
  (map_hom : Π {X Y : C} (f : C.hom X Y), D.hom (map_obj X) (map_obj Y))
  (id : ∀ (X : C), map_hom (C.id X) = D.id (map_obj X))
  (comp : ∀ {X Y Z : C} (f : C.hom X Y) (g : C.hom Y Z), map_hom (C.compose g f) = D.compose (map_hom g) (map_hom f))

-- Coercion from functor to function.
-- This only works for the object mapping (map_obj!).
-- For morphism mapping use functor_map defined below.
instance coe_functor_obj {C D : category} : has_coe_to_fun (functor C D) (λ f, C → D) :=
{
  coe := λ f, f.map_obj
}

def functor_map {C D : category} (F: functor C D) {X Y : C} (f : C.hom X Y) :  D.hom (F.map_obj X) (F.map_obj Y) := F.map_hom f

def is_full {C D : category} (F: functor C D) :=
  ∀ {X Y : C} (g : D.hom (F.map_obj X) (F.map_obj Y)), ∃ (f : C.hom X Y), (F.map_hom f) = g

def is_faithful {C D : category} (F: functor C D) :=
  ∀ {X Y : C} {f g : C.hom X Y} (h : functor_map F f = functor_map F g), f = g

end category_theory

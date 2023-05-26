import .category

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

class full {C D : category} {F: functor C D} :=
  (full : ∀ {X Y : C} (g : D.hom (F.map_obj X) (F.map_obj Y)), ∃ (f : C.hom X Y), (F.map_hom f) = g)

class faithful {C D : category} {F: functor C D} :=
  (faithful : ∀ {X Y : C} {f g : C.hom X Y} (h : functor_map F f = functor_map F g), f = g)

-- Creates the identity functor of a category.
-- This maps each object and morphism to itself.
def identity_functor (C : category) : functor C C :=
{
  map_obj := λ X : C, X,
  map_hom := λ X Y : C, λ f, f,
  id :=
    begin
      intro X,
      refl,
    end,
  comp :=
    begin
      intros,
      refl,
    end,
}
-- eg. use: 𝟙C : functor C C for the identity functor of category C
notation (name := identity_functor) `𝟙` := identity_functor

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

end category_theory
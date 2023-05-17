-- First attempt:
-- universes u

-- class category :=
--   (Obj : Type u)
--   (hom : Obj → Obj → Prop)
--   (compose : ∀ {X Y Z : Obj}, (hom X Y) → (hom Y Z) → (hom X Z))
--   (id : ∀ X : Obj, hom X X)
--   (left_id : ∀ {X Y : Obj} (f : (hom X Y)), compose (id X) f = f)
--   (right_id : ∀ {X Y : Obj} (f : (hom X Y)), compose f (id Y) = f)
--   (assoc : ∀ {X Y Z W : Obj} (f : (hom X Y)) (g : (hom Y Z)) (h : (hom Z W)),
--     compose (compose f g) h = compose f (compose g h))

-- Better version:
universes u v

class category :=
  -- attributes
  (obj     : Sort u)
  (hom     : Π (X Y : obj), Sort v)
  (id      : ∀ (X : obj), hom X X)
  (compose : Π {X Y Z : obj} (g : hom Y Z) (f : hom X Y), hom X Z)

  -- notation
  (infix (name := category_compose) `∘`:90 := compose)

  -- properties
  (left_id  : ∀ {X Y : obj} (f : hom X Y), f ∘ id(X) = f)
  (right_id : ∀ {X Y : obj} (f : hom X Y), id(Y) ∘ f = f)
  (assoc    : ∀ {X Y Z W : obj} (f : hom X Y) (g : hom Y Z) (h : hom Z W), h ∘ (g ∘ f) = (h ∘ g) ∘ f)
  -- done with category

class Isomorphism [C : category] {X Y : C.obj} (f : C.hom X Y) :=
  (g : C.hom Y X)
  (f_g : C.compose f g = C.id Y) -- would be nice to use ∘ instead of C.compose
  (g_f : C.compose g f = C.id X) -- same here

class SectionRetractionPair [C : category] {X Y : C.obj} (s : C.hom X Y) (r : C.hom Y X) :=
  (r_s : C.compose r s = C.id X) -- same here

class Monomorphism [C : category] {X Y Z : C.obj} (f : C.hom X Y) :=
  (mono : ∀ {g₁ g₂ : C.hom Z X}, C.compose f g₁ = C.compose f g₂ → g₁ = g₂) -- same here

class Epimorphism [C : category] {X Y Z : C.obj} (f : C.hom X Y) :=
  (epi : ∀ {g₁ g₂ : C.hom Y Z}, C.compose g₁ f = C.compose g₂ f → g₁ = g₂) -- same here

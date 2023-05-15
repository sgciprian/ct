universes u v 

class Category :=
  (C₀ : Sort u)
  (hom      : Π (X Y : C₀), Sort v)
  (id       : Π (X : C₀), hom X X)
  (compose  : Π {X Y Z : C₀} (g : hom Y Z) (f : hom X Y), hom X Z)
  (infix (name := category_compose) `∘`:90 := compose)

  -- Properties
  (left_id  : ∀ {X Y : C₀} (f : hom X Y), f ∘ id(X) = f)
  (right_id : ∀ {X Y : C₀} (f : hom X Y), id(Y) ∘ f = f)
  (assoc    : ∀ {X Y Z W : C₀} (f : hom X Y) (g : hom Y Z) (h : hom Z W), h ∘ (g ∘ f) = (h ∘ g) ∘ f)

class Isomorphism [C : Category] {X Y : C.C₀} (f : C.hom X Y) :=
  (g : C.hom Y X)
  (f_g : C.compose f g = C.id Y) -- would be nice to use ∘ instead of C.compose
  (g_f : C.compose g f = C.id X) -- same here

class SectionRetractionPair [C : Category] {X Y : C.C₀} (s : C.hom X Y) (r : C.hom Y X) :=
  (r_s : C.compose r s = C.id X) -- same here

class Monomorphism [C : Category] {X Y Z : C.C₀} (f : C.hom X Y) :=
  (mono : ∀ {g₁ g₂ : C.hom Z X}, C.compose f g₁ = C.compose f g₂ → g₁ = g₂) -- same here

class Epimorphism [C : Category] {X Y Z : C.C₀} (f : C.hom X Y) :=
  (epi : ∀ {g₁ g₂ : C.hom Y Z}, C.compose g₁ f = C.compose g₂ f → g₁ = g₂) -- same here


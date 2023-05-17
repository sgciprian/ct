universes u v

namespace category_theory

class category (Obj : Sort u) :=
  (hom : Π (X Y : Obj), Sort v)
  (compose : ∀ {X Y Z : Obj}, (hom X Y) → (hom Y Z) → (hom X Z))
  (id : ∀ X : Obj, hom X X)
  (left_id : ∀ {X Y : Obj} (f : (hom X Y)), compose (id X) f = f)
  (right_id : ∀ {X Y : Obj} (f : (hom X Y)), compose f (id Y) = f)
  (assoc : ∀ {X Y Z W : Obj} (f : (hom X Y)) (g : (hom Y Z)) (h : (hom Z W)),
    compose (compose f g) h = compose f (compose g h))

infixr `⟶`:90 := category.hom
infix (name := category_compose) `∘`:90 := category.compose
notation `𝟙` := category.id

class monomorphism {O : Sort u} [C : category O] {X Y : O} (f : X ⟶ Y) :=
  (mono : ∀ {Z : O} (g h : Z ⟶ X), ((g ∘ f) = (h ∘ f)) → (g = h))

class epimorphism {O : Sort u} [C : category O] {X Y : O} (f : X ⟶ Y) :=
  (epi : ∀ {Z : O} (g h : Y ⟶ Z), ((f ∘ g) = (f ∘ h)) → (g = h))

class isomorphism {O : Sort u} [C : category O] {X Y : O} (f : X ⟶ Y) :=
  (iso : ∃ (g : Y ⟶ X),((f ∘ g) = (𝟙 X)) ∧ ((g ∘ f) = (𝟙 Y)))

class isomorphism2 {O : Sort u} [C : category O] (N M : O) :=
  (hom : N ⟶ M)
  (inverse : M ⟶ N)
  (idl : hom ∘ inverse = 𝟙 N)
  (idr : inverse ∘ hom = 𝟙 M)

class initial {O : Sort u} [C : category O] {X : O} :=
  (map : ∀ (Y : O), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g)

class terminal {O : Sort u} [C : category O] {Y : O} :=
  (map : ∀ (X : O), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g)

--Functors
class functor {C D : Sort*} [category C] [category D] (F : C → D) :=
  (map : Π {X Y : C} (f : X ⟶ Y), F X ⟶ F Y)
  (id : ∀ (X : C), map (𝟙 X) = 𝟙 (F X))
  (comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ∘ g) = map f ∘ map g)

def functor_map {C D : Sort*} [category C] [category D] (F : C → D) [functor F] {X Y : C} (f : X ⟶ Y) : F X ⟶ F Y := functor.map f

class full {C D : Sort*} [category C] [category D] (F : C → D) [functor F] : Prop :=
  (full : ∀ {X Y : C} (g : F X ⟶ F Y), ∃ (f : X ⟶ Y), functor.map f = g)

class faithful {C D : Sort*} [category C] [category D] (F : C → D) [functor F] : Prop :=
  (faithful : ∀ {X Y : C} {f g : X ⟶ Y} (h : functor_map F f = functor_map F g), f = g)

structure natural_transformation {C D : Sort*} [category C] [category D] (F G : C → D) [functor F] [functor G] :=
  (map     : Π (X : C), F X ⟶ G X)
  (natural : ∀ {X Y : C} (f : X ⟶ Y), (functor_map F f) ∘ (map Y) = (map X) ∘ (functor_map G f))


--examples
instance nat_le_category : category (nat) :=
{
  hom := λ n m, n <= m,
  id := λ n, le_refl n,
  compose := λ _ _ _ f g, le_trans f g,
  left_id := λ _ _ _, by refl,
  right_id := λ _ _ _, by refl,
  assoc := λ _ _ _ _ _ _ _, by refl,
}

def nat_mul (n m : nat) : nat := n * m
-- instance nat_multp_category : category (nat) :=
-- {
--   Obj := nat,
--   hom := nat_mul,
--   id := λ _, begin
--     simp [nat_mul],
--   end,
--   compose := λ  n m p f g, begin
--     simp [nat_mul] at *,
--   end,
--   left_id := λ _ _ _, by refl,
--   right_id := λ _ _ _, by refl,
--   assoc := λ _ _ _ _ _ _ _, by refl,
-- }

end category_theory
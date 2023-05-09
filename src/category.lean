universes u

class category :=
  (Obj : Type u)
  (hom : Obj → Obj → Prop)
  (compose : ∀ {X Y Z : Obj}, (hom X Y) → (hom Y Z) → (hom X Z))
  (id : ∀ X : Obj, hom X X)
  (left_id : ∀ {X Y : Obj} (f : (hom X Y)), compose (id X) f = f)
  (right_id : ∀ {X Y : Obj} (f : (hom X Y)), compose f (id Y) = f)
  (assoc : ∀ {X Y Z W : Obj} (f : (hom X Y)) (g : (hom Y Z)) (h : (hom Z W)),
    compose (compose f g) h = compose f (compose g h))

instance nat_le_category : category :=
{
  Obj := nat,
  hom := λ n m, n ≤ m,
  id := λ n, le_refl n,
  compose := λ _ _ _ f g, le_trans f g,
  left_id := λ n m f, begin
    refl
  end,
  right_id := λ n m f, begin
    refl
  end,
  assoc := λ n m p q f g h, begin
    refl
  end,
}

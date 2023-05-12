namespace ct

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

end ct
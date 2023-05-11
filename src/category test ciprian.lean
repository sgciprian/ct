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

instance SET₁ : category :=
{
  obj := set (Sort u),
  hom := λ (A B : set (Sort u)), ∀ (f : Sort u → Sort u), ∀ (x ∈ A), (f x) ∈ B,
  id  := λ (A : set (Sort u)),
    begin
      -- goal impossible to prove
      sorry,
    end

}

instance SET₂ : category :=
{
  obj := set (Sort u),
  hom := λ (A B : set (Sort u)), ∃ (f : Sort u → Sort u), ∀ (x ∈ A), (f x) ∈ B,
  -- problematic since hom implies that there is at least one mapping between each pair of sets
  -- but i think there really is a mapping between each pair of sets?
  id  := λ (A : set (Sort u)),
    begin
      apply exists.intro id,
      intro x,
      intro p,
      rw id,
      exact p,
    end,
  compose :=
    begin
      intros,
      cases f with f hf,
      cases g with g hg,
      have t := g ∘ f,
      apply exists.intro t,
      intros x p,
      specialize hf x,
      have q := hf p,
      specialize hg (f x),
      have r := hg q,
      -- how do i use t = g.f
    end,
}
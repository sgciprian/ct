universes u v x

-- The previously defined Category, isomorphism and monomorphism
-- Made the obj a parameter, in order to make the types easier to understand
-- in the monoid, and other structures, which depend on a category.
-- Changed hom to morph, as what we have now represents a morphism, not the hom-set.

class category (obj : Sort u) :=  
  (morph : obj → obj → Sort v)
  (compose : ∀ {X Y Z : obj}, (morph X Y) → (morph Y Z) → (morph X Z))
  (id : ∀ (X : obj), morph X X)
  (left_id : ∀ {X Y : obj} (f : (morph X Y)), compose (id X) f = f)
  (right_id : ∀ {X Y : obj} (f : (morph X Y)), compose f (id Y) = f)
  (assoc : ∀ {X Y Z W : obj} (f : (morph X Y)) (g : (morph Y Z)) (h : (morph Z W)),
    compose f (compose g h) = compose (compose f g) h)

class isomorphism (O : Sort u) [C : category O] (N M : O) :=
   (hom : C.morph N M)
   (inverse : C.morph M N)
   (idl : C.compose hom inverse = C.id N)
   (idr : C.compose inverse hom = C.id M)

class monomorphism (O : Sort u) [C : category O] {X Y : O} (f : C.morph X Y) :=
(mono : ∀ {Z : O} (g h : C.morph Z X), ((C.compose g f) = (C.compose h f)) → (g = h))


-- definition of a monoid as stated in the lecture notes

class monoid (M : Sort u) [C : category M] :=
  (m : M → M → M)
  (e : M)
  (assoc : ∀ (X Y Z : M), m X (m Y Z) = m (m X Y) Z)
  (left_id : ∀ (X : M), m e X = X)
  (right_id : ∀ (X : M), m X e = X)

-- category Monoid(M,m,e) as defined in the lecture notes.
-- Only thing that I'm not certain about is whether we need to be stricter
-- with the type of O, in order to make it a "unique" *.

def MonoidCategory (O : Type u) [C : category O] [M : monoid O] : category O :=
  {
    morph := λ _ _, O,
    compose := λ _ _ _ f g, M.m f g,
    id := λ _, M.e,
    left_id :=
    begin
      intros _ _ f,
      exact M.left_id f
    end,
    right_id := 
    begin
      intros _ _ f,
      exact M.right_id f
    end,
    assoc := 
    begin
      intros X Y Z W f g h,
      exact M.assoc f g h
    end
  }

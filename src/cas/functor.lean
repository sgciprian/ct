import cas.category

namespace cas

  class functor (A B : category) :=

  -- mapping between objects
  (map_obj  : A.obj → B.obj)

  --mapping between morphisms
  (map_hom  : ∀ {x y : A.obj} (f : A.hom x y), B.hom (map_obj x) (map_obj y))

  -- T(id_A) = id_{T(A)} -- it keeps identities
  (id_map   : ∀ (x : A.obj), map_hom (A.id x) = B.id (map_obj x))

  -- T (f ∘ g) = T(f) ∘ T(g) -- it preserves composition
  (comp_map : ∀ {x y z : A.obj} (f : A.hom x y) (g : A.hom y z),
    map_hom (A.compose g f) = B.compose (map_hom g) (map_hom f))

end cas


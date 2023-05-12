import Category 

instance Poset : Category ℕ :=
  {
    hom := λ (X Y : ℕ), X ≤ Y, 
    id := λ X, le_refl X,
    compose := λ _ _ _ g f, le_trans f g,
    left_id := begin intros, refl end,
    right_id := begin intros, refl end,
    assoc := begin intros, refl end
  }

variables {X Y : ℕ} (f : Poset.hom X Y) (inverse : Poset.hom Y X)

instance PosetIsomorphism : Isomorphism f :=
  {
    g := inverse,
    f_g := rfl,
    g_f := rfl
  }

instance PosetSecRectPair : SectionRetractionPair f inverse :=
  {
    r_s := rfl
  }

instance PosetMonomorphism : Monomorphism f :=
  {
    mono := sorry
  }

instance PosetEpimorphism : Epimorphism f :=
  {
    epi := sorry
  }
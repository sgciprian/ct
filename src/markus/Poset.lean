import markus.Category

instance Poset : Category :=
  {
    C₀ := ℕ,
    hom := λ (X Y : ℕ), X ≤ Y, 
    id := λ X, le_refl X,
    compose := λ _ _ _ g f, le_trans f g,
    left_id := begin intros, refl end,
    right_id := begin intros, refl end,
    assoc := begin intros, refl end
  }

instance PosetIsomorphism {X Y : Poset.C₀} (f : Poset.hom X Y) (inverse : Poset.hom Y X) : Isomorphism f :=
  {
    g := inverse,
    f_g := rfl,
    g_f := rfl
  }

instance PosetSecRectPair {X Y : Poset.C₀} (f : Poset.hom X Y) (inverse : Poset.hom Y X) : SectionRetractionPair f inverse :=
  {
    r_s := rfl
  }

/-
instance PosetMonomorphism {X Y Z : ℕ} (f : X ≤ Y) : Monomorphism f :=
  {
    mono := sorry
  }

instance PosetEpimorphism {X Y : ℕ} (f : Poset.hom X Y) : Epimorphism f :=
  {
    epi := sorry
  }
-/
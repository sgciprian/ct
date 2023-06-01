import category

open category_theory

-- C × D
-- product category of C and D
def Product (C D : category) : category :=
{
  -- Objects are ordered pairs (c, d)
  C₀ := C × D,
  
  -- Morphisms are ordered pairs of morphisms
  -- in C and in D
  hom := λ p p', (C.hom p.fst p'.fst) × (D.hom p.snd p'.snd), 

  -- 𝟙(c, d) = (𝟙c, 𝟙d)
  id  := λ p, (𝟙C p.fst, 𝟙D p.snd),

  -- Composition composes each morphism in the pair in its
  -- original category.
  compose := λ {p q r} (g : (C.hom q.fst r.fst) × (D.hom q.snd r.snd))
                       (f : (C.hom p.fst q.fst) × (D.hom p.snd q.snd)), 
             ((C.compose g.fst f.fst), (D.compose g.snd f.snd)),

  -- We can use the proofs from function.comp.
  left_id :=
    begin
      intros,
      simp,
      rw C.left_id,
      rw D.left_id,
      simp,
    end,
  right_id :=
    begin
      intros,
      simp,
      rw C.right_id,
      rw D.right_id,
      simp,
    end,
  assoc :=
    begin
      intros,
      simp,
      rw C.assoc,
      rw D.assoc,
    end,
}

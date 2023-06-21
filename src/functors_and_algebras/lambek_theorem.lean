import category
import functors
import morphisms
import functors_and_algebras.f_algebra
import functors_and_algebras.tools
import functors_and_algebras.fusion_property
import functors_and_algebras.algebra_category

namespace category_theory

def algebra_f {C : category} {F : functor C C} (alg : Falgebra F) : Falgebra F := {
  object := F.map_obj alg.object,
  function := (F.map_hom alg.function),
}

lemma inverse_uniqueness {C : category} {A B : C.C₀} : 
  ∀ (f : C.hom A B) (g h : isomorphism f), g.inverse = h.inverse :=
begin
  intros,
  -- have h1 : g = C.compose
  rw [←C.left_id g.inverse],
  rw [←h.idl],
  rw [C.assoc],
  rw [g.idr],
  rw [C.right_id],
end 

-- def lambek_theorem {C : category} {F : functor C C} (algebra : initial (AlgebraCategory F)) 
--   : is_iso algebra.object.function (algebra.exist_morph (algebra_f algebra.object)).morph :=
--   begin
--     simp [is_iso],
--     -- apply classical.,
--     split,
--     {
--       simp [(algebra.exist_morph (algebra_f algebra.object)).square_proof],
--       have h1 : (algebra_f algebra.object).function = F.map_hom algebra.object.function := by refl,
--       rw h1,
--       simp [←F.comp],
--       simp [←F.id],
--       have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
--       have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
--         C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
--       simp [h1 h2],
--       have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
--       begin
--         simp [C.right_id],
--         simp [F.id],
--         simp [C.left_id],
--       end,
--       have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
--       simp [←h4], 
--     },
--     {
--       have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
--       have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
--         C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
--       simp [h1 h2],
--       have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
--       begin
--         simp [C.right_id],
--         simp [F.id],
--         simp [C.left_id],
--       end,
--       have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
--       simp [←h4], 
--     },
--   end

  def lambek_theorem {C : category} {F : functor C C} (algebra : initial (AlgebraCategory F))
  : ∀ iso : isomorphism algebra.object.function, iso.inverse = (algebra.exist_morph (algebra_f algebra.object)).morph :=
begin
  intros,
  have h1 := inverse_uniqueness algebra.object.function iso {
    inverse := (algebra.exist_morph (algebra_f algebra.object)).morph,
    idl :=
    begin
        have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
      have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
        C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
      simp [h1 h2],
      have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
      begin
        simp [C.right_id],
        simp [F.id],
        simp [C.left_id],
      end,
      have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
      simp [←h4], 
    end,
    idr :=
    begin
      simp [(algebra.exist_morph (algebra_f algebra.object)).square_proof],
      have h1 : (algebra_f algebra.object).function = F.map_hom algebra.object.function := by refl,
      rw h1,
      simp [←F.comp],
      simp [←F.id],
      have h1 := fusion algebra (algebra_f algebra.object) algebra.object algebra.object.function,
      have h2 : C.compose algebra.object.function (algebra_f algebra.object).function =
        C.compose algebra.object.function (F.map_hom algebra.object.function) := by refl,
      simp [h1 h2],
      have h3 : C.compose (C.id algebra.object.object) algebra.object.function = C.compose algebra.object.function (F.map_hom (C.id algebra.object.object)) := 
      begin
        simp [C.right_id],
        simp [F.id],
        simp [C.left_id],
      end,
      have h4 := algebra.is_unique {morph := (C.id algebra.object.object), square_proof := h3},
      simp [←h4], 
    end,
  },
  simp [h1],
end

end category_theory
universes u v

namespace category_theory

structure category :=
  --attributes
  (C₀     : Sort u)
  (hom     : Π (X Y : C₀), Sort v)
  (id      : Π (X : C₀), hom X X)
  (compose : Π {X Y Z : C₀} (g : hom Y Z) (f : hom X Y), hom X Z)
  --axioms
  (left_id  : ∀ {X Y : C₀} (f : hom X Y), compose f (id X) = f)
  (right_id : ∀ {X Y : C₀} (f : hom X Y), compose (id Y) f = f)
  (assoc    : ∀ {X Y Z W : C₀} (f : hom X Y) (g : hom Y Z) (h : hom Z W), compose h (compose g f) = compose (compose h g) f)

instance coe_category : has_coe_to_sort category (Sort u) :=
{
  coe := λ c, c.C₀
}

lemma simp_comp_left {C : category} {X Y Z : C} {f₁ f₂ : C.hom Y Z} {g : C.hom X Y} : f₁ = f₂ → C.compose f₁ g = C.compose f₂ g :=
  begin
    cc,
  end

lemma simp_comp_right {C : category} {X Y Z : C} {f : C.hom Y Z} {g₁ g₂ : C.hom X Y} : g₁ = g₂ → C.compose f g₁ = C.compose f g₂ :=
  begin
    cc,
  end

--notation
--infixr `⟶`:90 := category.hom
--infix (name := category_compose) `∘`:90 := category.compose
notation (name := category_identity) `𝟙` := category.id

end category_theory
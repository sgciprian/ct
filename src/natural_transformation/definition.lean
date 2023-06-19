import category
import functors

namespace category_theory 

structure natural_transformation {𝒞 𝒟 : category} (F G : 𝒞 ⇒ 𝒟) :=
  (α : Π (X : 𝒞) , 𝒟.hom (F.map_obj X) (G.map_obj X))
  (naturality_condition : ∀ {X Y : 𝒞} (f : 𝒞.hom X Y), 
    𝒟.compose (G.map_hom f) (α X)  = 
    𝒟.compose (α Y) (F.map_hom f)
  )

  -- notation
  infixr `≫`:75 := natural_transformation


end category_theory

import .category
import .functors

namespace category_theory 

structure natural_transformation {C D : category} (F G : functor C D) :=
  (α : Π (X : C.C₀) , D.hom (F.map_obj X) (G.map_obj X))
  (naturality_condition : ∀ {X Y : C.C₀} (f : C.hom X Y), 
    D.compose (G.map_hom f) (α X)  = 
    D.compose (α Y) (F.map_hom f)
  )

end category_theory
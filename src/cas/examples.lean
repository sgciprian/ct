import cas.category
import cas.functor

namespace cas

  -- Type with only two objects
  inductive duo : Type
  | A : duo 
  | B : duo

  -- Arrows in both directions and also as id.
  def fun_duo : duo → duo → Prop
  | _ _ := true

  -- Duo type as category with fun
  instance duo_as_cat : category :=
  {
    obj := duo,
    hom := fun_duo,
    id := begin intro, trivial, end,
    compose := begin intros, trivial, end,
    left_id := begin intros, trivial, end,
    right_id := begin intros, trivial, end,
    assoc := begin intros, trivial, end,
  }
  
  -- Function to map A to B and B to A
  def switch : duo → duo
  | duo.A := duo.B
  | _ := duo.A
  
  -- Switch function as functor on the Duo category.
  instance duo_as_functor : functor cas.duo_as_cat cas.duo_as_cat :=
  {
    map_obj := switch,
    map_hom := begin intros, trivial, end,
    comp_map := begin intros, trivial, end,
    id_map := begin intros, trivial, end,
  }

end cas

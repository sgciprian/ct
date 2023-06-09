-- Example
-- Stream
import .coalgebra ..instances.types_category
namespace category_theory

universe u

def stream (α : Type u) := nat → α

def head {α : Type u} (s : stream α) : α := s 0

def tail {α : Type u} (s : stream α) : stream α := λ i, s (i+1)

-- def map_stream {α β : Type*} (f : α → β) : stream α → stream β
-- | (stream.cons h t) := stream.cons (f h) (map_stream t)

-- theorem map_stream_id {X : Type*} : map_stream (Types.id X) = Types.id (stream X) :=
-- begin
--   funext s,
--   induction s with h t ih,
--   simp [map_stream, ih],
--   refl

-- end

-- theorem map_stream_comp {X Y Z : Type*} (f : X → Y) (g : Y → Z) :
--   map_stream (Types.compose g f) = Types.compose (map_stream g) (map_stream f) :=
-- begin
--   funext s,
--   induction s with h t ih,
--   simp [map_stream, ih],
--   refl
-- end

-- def stream_functor : functor Types Types :=
-- {
--   map_obj := λ α, (stream α),
--   map_hom := λ α β f, map_stream f,
--   id := λ α, map_stream_id,
--   comp := λ α β γ f g, map_stream_comp f g,
-- }

def stream_functor (α : Type u) : functor Types Types :=
{
  map_obj := λ X, α × X,
  map_hom := 
    begin
      intros X Y f,
      intro p,
      cases p with a x,
      exact (a, f x)
    end,
  id := 
    begin
      intro X,
      simp,
      funext x,
      cases x,
      refl
    end,
  comp := 
    begin
      intros X Y Z f g,
      simp,
      funext p,
      cases p with a x,
      simp,
      refl
    end
}

def stream_coalgebra {α : Types.C₀} : coalgebra (stream_functor α) :=
{
  A := stream α,
  ϕ := λ s, (head s, tail s)
}

end category_theory
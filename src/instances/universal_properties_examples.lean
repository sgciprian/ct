import universal_properties
import .Set_category

namespace category_theory

lemma empty_set_initial_in_Set : isInitial Set empty :=
begin
  intros B f g,
  funext x, -- Proving functions equality pointwise
  cases x, -- There are no elements in the empty set, so we can use cases to handle all possible cases (i.e., none)
end

lemma singleton_terminal_in_Set (b : Set.C₀) (h : subsingleton b) : isTerminal Set b :=
begin
  intros A f g,
  funext a, -- Proving functions equality pointwise
  apply subsingleton.elim (f a) (g a), -- Using the subsingleton property to conclude f a = g a
end

end category_theory
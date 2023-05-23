import .category

namespace category_theory

def isInitial (C : category) (A : C.C₀) : Prop :=
  ∀ (B : C.C₀), ∃ (f g : C.hom A B), f = g

structure initialObject (C : category) (A : C.C₀) :=
  (property : isInitial C A)

def isTerminal (C : category) (B : C.C₀) : Prop :=
  ∀ (A : C.C₀), ∃ (f g : C.hom A B), f = g

structure terminalObject (C : category) (B : C.C₀) :=
  (property : isTerminal C B)
  
end category_theory
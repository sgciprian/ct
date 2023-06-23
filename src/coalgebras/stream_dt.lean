universe u

-- inductive stream (α : Type u) : Type u
-- | cons (head : α) (tail : stream) : stream

-- def head {α : Type*} (s : stream α) : α :=
-- match s with
-- | cons h _ := h
-- end

-- def tail {α : Type*} (s : stream α) : stream α :=
-- match s with
-- | cons _ t := t
-- end


def stream (α : Type u) := nat → α

def cons {α : Type u} (a : α) (s : stream α) : stream α
| 0       := a
| (n + 1) := s n

def head {α : Type u} (s : stream α) : α := s 0

def tail {α : Type u} (s : stream α) : stream α := λ i, s (i+1)

def nth {α : Type u} (s : stream α) (n : nat) : α := s n

def map {α β : Type u} (f : α → β) (s : stream α) : stream β := λ n, f (nth s n)

def iterate {α : Type u} (f : α → α) (a : α) : stream α := λ n, nat.rec_on n a (λ n r, f r)

def corec {α β : Type u} (f : α → β) (g : α → α) : α → stream β := λ a, map f (iterate g a)
def corec' {α β : Type u} (f : α → β × α) : α → stream β := corec (prod.fst ∘ f) (prod.snd ∘ f)

-- def unfolds {α β : Type u} (g : α → β) (f : α → α) (a : α) : stream β := corec g f a
def unfolds {α β : Type u} (f : α → β × α) (a : α) : stream β := corec' f a
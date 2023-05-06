import Lean

-- Checking simple syntax
variable (b : Prop)
#check And (Not b) b
#check trivial

-- Example of working with types form the tutorial
variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose := g (f x)
def doTwice := h (h x)
def doThrice := h (h (h x))

#print compose
#print doTwice
#print doThrice

-- Check the type of a built-in function
#print List.cons

-- Example with proofs from the tutorial
def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof : Prop → Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))
axiom aad_comm (p q : Prop) : Proof (Implies (And p p) (And q p))


variable (p q : Prop)
variable (hq : q)
#check and_comm p q     -- Proof (Implies (And p q) (And q p))
#check aad_comm p False -- Since `aad_comm` was an axiom this compiles even though it is not logically sound
#print Not q
#print and_comm

-- Example of a theorem with a proof
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun _ : q => hp

#print t1


-- This is here so that it can be run from a terminal.
-- It will give a return value of 1 if something does not check out in the file.
def main : IO UInt32 := do
  IO.println "All good!"
  return 0
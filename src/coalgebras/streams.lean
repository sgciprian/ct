-- Example
-- Stream
import .final_coalgebra ..instances.types_category ..universal_properties .stream_dt 

universe u

namespace category_theory

def stream_functor (α : Type*) : functor Types Types :=
{
  map_obj := λ X, α × X,
  map_hom := λ X Y f, λ p, (p.fst, f p.snd),
  id := 
    begin
      intro X,
      funext x,
      cases x,
      refl
    end,
  comp := 
    begin
      intros X Y Z f g,
      funext p,
      cases p with a x,
      simp,
      refl
    end
}

def stream_coalgebra {α : Types.C₀} : (coalgebra_category (stream_functor α)).C₀ :=
{
  object := stream α,
  morphism := λ s, (head s, tail s)
}

lemma unfold_head {S : Types.C₀} {f : Types.hom S ((stream_functor S).map_obj S)} {x:S} :
  head (unfolds f x) = (f x).fst :=
begin
  unfold unfolds,
  simp [head],
  refl,
end

axiom unfold_tail_lemma {α β  : Types.C₀} {f : α → β × α} {x:α} :
  tail (unfolds f x) = unfolds f (f x).snd

lemma unfold_tail {α β  : Types.C₀} {f : α → β × α} {x:α} :
  tail (unfolds f x) = unfolds f (f x).snd :=
begin
  -- - Unfold the definitions
  unfold unfolds,
  -- simp [tail],
  -- funext n,

  -- induction n with n IH,
  -- { -- Base case: n = 0
  --   refl },
  -- { -- Inductive case: n = nat.succ k
  --   -- Use the induction hypothesis
  --   -- Unfold the definitions
  --   -- rw [nat.add_succ, nat.add_zero],
  --   -- rw [nat.add_succ, nat.add_zero] at IH,
  --   rw [corec', corec],
    

    
  --   rw [ <-corec, <-corec'],
    
  --   have h : corec' f x (n.succ + 1)
  --     = (f (corec' f x (n.succ))).fst := by refl,
  --   rw [h],

  --   -- simp [IH],
  --   -- Simplify the inductive step
  --   -- rw unfold_tail_lemma,
  --   -- Simplify using the given assumptions and the definition of `nat.rec`
  --   simp only [Types.comp_apply],
  --   rw IH },





  -- Apply simplifications
  simp [corec', corec, map, tail],
  -- Use extensionality to prove equality pointwise
  funext n,
  -- Simplify nth expressions
  simp [nth], 
  simp [function.comp],
  
  -- have h : (f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n + 1))).fst
  --     = (f ((f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n))).snd)).fst := by refl,
  -- rw [h],

  rw [iterate],
  rw iterate,
  simp [function.comp],

  induction n with n IH,
  { -- Base case: n = 0
    refl },
  { -- Inductive case: n = nat.succ k
    -- Use the induction hypothesis
    
    -- refl,
  --   -- Simplify the inductive step
    -- specialize IH,
    -- simp only [prod.fst, prod.snd] at IH,
    -- simp [IH],
    -- rw Types.assoc f,
    
    -- congr,
    -- exact H,
    -- simp [IH], 

    -- have h : (f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n + 1))).fst
    --     = (f ((f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n))).snd)).fst := by refl,
    -- rw [h] at IH,

    -- have h : corec' f (f x).snd n = corec' f x (n + 1) := by simp [IH],
    -- rw [h],
    simp [function.comp],
    have h : (f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n.succ + 1))).fst
      = (f ((f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n + 1))).snd)).fst := by refl,
    rw [h],

  -- simp [function.comp],
  
    -- simp [IH],
    have h : (f (f (nat.rec (f x).snd (λ (n : ℕ) (r : α), (f r).snd) n)).snd).fst
      = (f ((f (nat.rec x (λ (n : ℕ) (r : α), (f r).snd) (n + 1))).snd)).fst := begin
        ,
      end,
    rw [h],
    
    congr,

    refl,
  },
end

def unfold_homomorphism  {S : Types.C₀} (A : coalgebra (stream_functor S)) : f_coalgebra_homomorphism A (stream_coalgebra) := 
{
  morphism := unfolds A.morphism,
  proof := 
  begin
    funext x,

    have simp_left : Types.compose stream_coalgebra.morphism (unfolds A.morphism) x
    = stream_coalgebra.morphism ((unfolds A.morphism) x) := begin refl end,
    rw simp_left,

    have simp_right : Types.compose ((stream_functor S).map_hom (unfolds A.morphism)) A.morphism x =
    ((stream_functor S).map_hom (unfolds A.morphism)) (A.morphism x)
     := by refl,
    rw simp_right,
    
    -- -- funext n,
    -- cases x,
    -- cases (A.morphism x) with a s,


    have h1 : stream_coalgebra.morphism (unfolds A.morphism x) 
    = (head (unfolds A.morphism x), tail (unfolds A.morphism x))  := by refl,
    rw [h1],

    have h2 : (head (unfolds A.morphism x), tail (unfolds A.morphism x))
      = ((A.morphism x).fst, tail (unfolds A.morphism x)) := by refl,
    rw [h2],

    -- unfold tail,
    -- cases (A.morphism x) with a s,
    -- simp,
    

    have h3 : (stream_functor S).map_hom (unfolds A.morphism) (A.morphism x)
      = ((A.morphism x).fst, (unfolds A.morphism (A.morphism x).snd)) := by refl,
    rw [h3],

    rw unfold_tail_lemma,

  end,
} 


def proof_stream_is_final {α : Types.C₀} : final_coalgebra (stream_functor α) := 
{
  obj := stream_coalgebra,
  anamorphism := unfold_homomorphism,
  -- unique := 
  --   begin
  --     intros A f,
  --     rw unfold_homomorphism,
  --     cases f,

  --     have h : f_morphism = unfolds A.morphism := 
  --     begin
  --       funext x,


  --       -- have temp1 : unfolds A.morphism x = stream.cons (A.morphism x).fst (unfolds A.morphism (A.morphism x).snd) := by refl,
  --       -- simp [temp1],

  --       -- have temp1 : unfolds A.morphism x = stream.cons (A.morphism x).fst (unfolds A.morphism (A.morphism x).snd) := by refl,
  --       -- simp [temp1],


  --       funext n,
  --       induction n,
  --       case nat.zero{ -- Case n = 0
  --         have temp1 : unfolds A.morphism x 0 = A.morphism (Either.left Singleton.star) := by refl,
  --         simp [temp1],

  --       },
  --       case nat.succ{ -- Case n > 0

  --         have h : (unfolds A.morphism x) n_n.succ 
  --           = cons (A.morphism x).fst ((unfolds A.morphism (A.morphism x).snd) n_n) := by refl,
  --         simp [h],

  --         have h : f_morphism x n_n.succ = ((unfolds A.morphism) x n_n.succ) := by refl,
  --         simp [h],
  --       },
  --       intros c f,
  --       rw unfold_homomorphism,
  --       cases f,
  --     end,

  --   end
}

end category_theory
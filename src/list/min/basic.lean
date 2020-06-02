import data.list.basic tactic.linarith
import list.lemmas.long_lemmas  misc_lemmas


open list
/-- The minimum element of a non-empty list-/
def list.min {X : Type*} [decidable_linear_order X] :
Π (L : list X), (L ≠ []) → X
| ([]) hL := false.elim $ hL rfl
| (x :: []) hL := x
| (x :: y :: L) _ := min x (list.min (y :: L) dec_trivial)

/--extended version of list.min on lists of integers that maps the empty list to 0-/
def list.min' (L : list ℤ) : ℤ :=
if h : L = [] then 0 else list.min L h


/--If we have two non-empty lists of the same length and for each index, elements with the same
   index differ by at most d, then their minimums differ by at most d-/
theorem list.min_change (L M : list ℤ) (hL : L ≠ []) (hLM : L.length = M.length) (hM : M ≠ []) (d : ℤ)
(hdist : ∀ (i : ℕ) (hiL : i < L.length) (hiM : i < M.length), abs (L.nth_le i hiL - M.nth_le i hiM) ≤ d) :
  abs (L.min hL - M.min hM) ≤ d :=
begin
  -- if L = nil, that contradicts hL
  cases L with n Ln,
    contradiction,
  -- L = (n :: Ln)
  revert n M, -- so the inductive hypothesis does not depend on n or M
  induction Ln with n1 Ln1 IH,
    
    -- base case : Ln = nil (so L = [n])
    {
      intros n M hM hL hLM hdist,
      change 1 = length M at hLM, -- as L = [n], and length [n] = length (n :: nil) = 1 by definition
      symmetry' at hLM, -- change 1 = length M to length M = 1
      rw length_eq_one at hLM, -- now hLM implies M is a singleton
      cases hLM with m hLM, -- say M = [m], for some a of type ℕ 
      simp only [hLM],
      show abs (n - m) ≤ d, /- because by def of list.min the minimum of a singleton 
                               is its only element -/
      convert hdist 0 (zero_lt_one) _, -- that is true because by hdist, abs (L.nth_le 0 hiL - M.nth_le 0 hiM) ≤ d
      -- have already told Lean i is 0 and 0 < 1 (which is the length of [n] by def)
      -- prove 0 < length M
        swap,
        {rw hLM,
        exact zero_lt_one},
      /- now prove m = nth_le M 0 _ (which convert reduced the goal to as it Lean noticed
                                     all other similarities to hdist)-/
      simp only [hLM], --
      refl, -- by def of nth_le
    },

     --inductive step : Ln = (n1 :: Ln1)
    { intros n M hM hL hLM hdist,
      -- if M = nil, that contradicts hM
      cases M with m Mm,
        contradiction,
      -- now M = (m :: Mm)
      -- but if Mm = nil, then by hLM length (n :: n1 :: Ln1) = length (m :: nil). Contradiction!
      cases Mm with m1 Mm1, 
        cases hLM,
      -- so M = (m :: m1 :: Mm1)
      unfold list.min, /- changes list.min (n :: n1 :: Ln1) hL to min n (list.min (n1 :: Ln1) _)
                           and list.min (m :: m1 :: Mm1) hM to min m (list.min (m1 :: Mm1) _)
                           (third constructor of list.min)-/
      /- we want to use the inductive hypothesis with M being (m1 :: Mm1)-/
      replace hLM := nat.succ_inj hLM, -- get : length (n1 :: Ln1) = length (m1 :: Mm1)
      -- the following is the version of hdist for M being (m1 :: Mm1)
      have hyp : (∀ (i : ℕ) (hiL : i < length (n1 :: Ln1)) (hiM : i < length (m1 :: Mm1)),
                 abs (nth_le (n1 :: Ln1) i hiL - nth_le (m1 :: Mm1) i hiM) ≤ d),
        intros i hiL hiM,
        exact hdist (i + 1) (nat.succ_lt_succ hiL) (nat.succ_lt_succ hiM), -- follows from hdist
      /- use the inductive hypothesis to get (h : abs (list.min (n1 :: Ln1) _ - list.min (m1 :: Mm1) _) ≤ d)
         (the other hypotheses, that the lists are non-empty, are true by decidability)-/
      have h := IH n1 (m1 :: Mm1) dec_trivial dec_trivial hLM hyp,
      have hmn : abs (n - m) ≤ d,
        exact hdist 0 dec_trivial dec_trivial, -- n, m are the 0th elements, so holds by hdist
      exact abs_min_sub_min hmn h} -- (see misc_lemmas)
end


/--If we have two lists of the same length and for each index, elements with the same
   index differ by at most some non-negative value d, then their extended minimums (min') differ by at most d-/
lemma list.min'_change (L M : list ℤ) (hLM : L.length = M.length) (d : ℤ) (hd : 0 ≤ d)
(hdist : ∀ (i : ℕ) (hiL : i < L.length) (hiM : i < M.length), abs (L.nth_le i hiL - M.nth_le i hiM) ≤ d) :
  abs (L.min' - M.min') ≤ d := 
  begin
  /- if M and L are non-empty, this is basically proven by the lemma above, because of
     how list.min' is defined.
     Therefore we prove the empty-list-case separately-/
  cases M with m Mn,
    -- M = nil (so hLM is : length L = length nil)
    {rw length at hLM, -- length nil = 0 by def of length
    rw length_eq_zero at hLM, -- length L = 0 ↔ L = nil
    rw hLM,
    -- now this is true by the definition of list.min' and hd
    unfold list.min',
    split_ifs,
      {exact hd}, -- case where nil = nil
      {contradiction},}, -- case where ¬ (nil = nil), a contradiction

  -- M = (m :: Mn)  
  /- now this is true by lis.min_change, but we first need to show M and N are non-empty-/
  {have hM : ¬ (m :: Mn : list ℤ) = nil := by simp,
  have hL : ¬ L = nil, 
    {apply ne_nil_of_length_pos, -- prove 0 < length L instead
    rw hLM,
    exact dec_trivial,}, -- true by decideability

  unfold list.min',
  split_ifs, -- (L = nil)-case killed immediately 
  exact list.min_change L (m :: Mn) hL hLM hM d hdist,}, 

  end
  

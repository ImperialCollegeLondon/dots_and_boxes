import data.list.basic tactic.linarith
import list.lemmas.long_lemmas


open list


/--Two lists are equal except one entry differs by at most d-/
structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ) --entry in which the lists differ
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n) --lists are equal otherwise
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d) -- differing entries differ by at most d



/--reflexivity of list.modify for non-empty lists-/
def list.modify_refl {L : list ℤ } {d : ℤ} (h : 0 < length L) (p : 0 ≤ d): list.modify L L d :=
{ n := 0, -- can choose an arbitrary entry in the list, as they differ by 0 everywhere
  ha := h,
  hb := h,
  heq := by refl,
  bound := begin 
           cases L with m M, 
             -- L = nil
             exfalso, -- contradicts h : 0 < length L
             exact nat.not_succ_le_zero 0 h, 
           -- L = (m :: M)
           rw nth_le, -- get goal abs(m-m) ≤ d
           simp only [abs_zero, add_right_neg, sub_eq_add_neg], -- left side is zero
           exact p,
           end
}


/--Two lists that are equal except one entry differs by at most d have equal length-/
theorem eq_size_of_modify_list {l1 l2 : list ℤ } {d : ℤ} (h : list.modify l1 l2 d) : l1.length = l2.length :=
begin
  -- split list.modify condition into its fields
  cases h, 
  -- as the lists below are equal by h_heq, their length must be equal
  have P : length(remove_nth l1 h_n) = length(remove_nth l2 h_n), 
    rw h_heq, --which is h.heq
    rw length_remove_nth l1 h_n h_ha at P, /- lemma says, if n < length L , then length (remove_nth L n) = 
                                              length L - 1    for any list L, natural number n -/ 
    rw length_remove_nth l2 h_n h_hb at P,  
  --need this for finish to work
  have Q : ¬ h_n < 0, 
    simp, -- follows as h.n is a natural number
  /- Now  P gives the result by cancelling -1 on both sides, but this
     only works if both lists have length > 0. Hence split into easy cases 
     and let Lean do the rest by itself-/
  cases l1, dsimp at h_ha,
  exfalso, finish,
  cases l2, dsimp at h_hb,
  exfalso, finish, 
  finish, 
  end


/--Two lists that are equal except one entry differs by at most d are element-
wise equal in all entries except the one at which they differ-/
theorem list.modify_same {A : list ℤ} {B : list ℤ} {d : ℤ}
  (h : list.modify A B d) (m : ℕ) (hmA : m < A.length) (hmB : m < B.length)
  (hmn : h.n ≠ m) : A.nth_le m hmA = B.nth_le m hmB :=
begin
  have H : length A = length B, 
    exact eq_size_of_modify_list h,-- exactly the conclusion of the theorem above

  cases h, 

  /- rewrite to put h.heq in the form
     take h_n A ++ tail (drop h_n A) = take h_n B ++ tail (drop h_n B) -/
  rw remove_nth_eq_nth_tail at h_heq, 
  rw modify_nth_tail_eq_take_drop at h_heq,
  rw remove_nth_eq_nth_tail at h_heq, 
  rw modify_nth_tail_eq_take_drop at h_heq,
  /- from this we want to derive that take h_n A = take h_n B and
     tail (drop h_n A) = tail (drop h_n B) ,
     because we will formuate nth_le through head, take and drop later-/
  have p : length (tail (drop h_n A)) = length (tail (drop h_n B)), rw length_tail,
    rw length_tail, 
    rw length_drop, 
    rw length_drop,
    rw H, 
  have h_eq_left : take h_n A = take h_n B , 
    exact append_inj_right' h_heq p,
  have h_eq_right : tail (drop h_n A) = tail (drop h_n B), 
    exact append_inj_left' h_heq p,
  
  rw ← head_reverse_take, rw ← head_reverse_take, --get rid of nth_le

  -- state of first goal : head (reverse (take (m + 1) A)) = head (reverse (take (m + 1) B))
  
  /-now we need to consider where the lists could have been modified in 
    relation to m+1 so we can show both sides give the same entry and it is not the 
    modified one-/
  have m_cases : (m+1) ≤ h_n ∨ h_n < (m+1) , 
    exact le_or_lt (m + 1) h_n,

  cases m_cases,
  -- (m+1) ≤ h_n
  rw take_lemma m_cases h_eq_left, --solves goal as both sides will be the same
                                   --(for the lemma, see list.lemmas.long_lemmas)

  -- h_n < (m+1)

  /-this time h_eq_right will give the result, because we will use the
    lemma take_drop_head_eq (see list.lemmas.long_lemmas) 
    But first we need the necessary assumptions for take_drop_head_eq,
    which will be h1 and hmA/hmB-/
  rw nat.lt_iff_add_one_le at hmA, 
  rw nat.lt_iff_add_one_le at hmB, 
  
  
  have h1 : 1 ≤ m,
  cases m,
    -- m = 0 => goal : 1 ≤ 0
    exfalso,
    have hn_0 : h_n = 0, 
      rw nat.lt_add_one_iff at m_cases, -- for all a, b in ℕ, a < b + 1 ↔ a ≤ b
      exact nat.eq_zero_of_le_zero m_cases, -- for all n in ℕ, if n ≤ 0 then n = 0
    exact false.elim (hmn hn_0), --hypotheses exactly contradict each other

    -- goal : 1 ≤ nat.succ m
    exact dec_trivial,

  --now we have all we need to use take_drop_head_eq
  rw take_drop_head_eq h1 hmA,
  rw take_drop_head_eq h1 hmB,

  -- from h_eq_right we can derive the following, which soves the main goal 
  have P : tail (drop (m - 1) A) = tail (drop (m - 1) B),
  {
   rw tail_drop, --(see list.lemmas.simple)
   rw tail_drop,
   rw tail_drop at h_eq_right,
   rw tail_drop at h_eq_right,
   -- we want to use drop_lemma. For that we need the following hypothesis
   have h2 : nat.succ h_n ≤ nat.succ (m-1),
     rw nat.succ_le_succ_iff, -- for all m, n in ℕ, succ m ≤ succ n ↔ m ≤ n
     rw nat.lt_add_one_iff at m_cases, -- for all a, b in ℕ, a < b + 1 ↔ a ≤ b
     apply nat.le_pred_of_lt, -- for all m, n in ℕ, if m < n, then m ≤ n - 1
     exact lt_of_le_of_ne' m_cases hmn, -- for all a, b in ℕ, if a ≤ b and a ≠ b, then a < b

   exact drop_lemma h2 h_eq_right, --(for the lemma, see list.lemmas.long_lemmas)
  },
  rw P,

  refl, -- trivial assumption needed for modify_nth_tail_eq_take_drop in line 75
  
  refl, -- same trivial assumption needed for modify_nth_tail_eq_take_drop in line 77

  
end


/--symmetry of list.modify-/
def list.modify.symm (A B : list ℤ) (d : ℤ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n, -- still differ in the same place
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm, -- by symmetry of = in m.heq
  bound := by rw [←neg_sub, abs_neg]; exact m.bound -- as abs(a-b) = abs(b-a) for integers a,b
}



/--If you remove the same entry, that is not the modified one from
both modified lists, you get a modified list-/
def list.modify_remove_nth {L1 : list ℤ} {L2 : list ℤ} {d : ℤ}
  (h : list.modify L1 L2 d)  (m : ℕ) (h_neq : m ≠ h.n):
  list.modify (remove_nth L1 m) (remove_nth L2 m) d:=
begin
/-if index m is not in the list, then remove_nth L m = L, for any list L, so 
  we can separate into the cases m < length L1 and length L1 ≤ m-/
by_cases hm : m < length L1,
swap, -- we solve the second goal first, because it is easier

-- ¬ (m < length L1)
{push_neg at hm, -- ¬ (m < length L1) is defined as length L1 ≤ m
 have x1 : remove_nth L1 m = L1,
   exact remove_nth_large_n L1 hm,
 rw x1,
 rw (eq_size_of_modify_list h) at hm,
 have x2 : remove_nth L2 m = L2,
   exact remove_nth_large_n L2 hm,
 rw x2,
 exact h,
},

-- m < length L1

/-this time we actually need to prove the existence of all 5 fields of
  list.modify-/
have hlength : length L1 = length L2, -- will need this to get heq
  exact eq_size_of_modify_list h,
cases h, --split h into fields
/-the entry at which the lists differ depends on h_n, where L1 and L2 differ.
  If m is less than h_n, then removing m shifts the index they differ in one
  space to the front. Otherwise, as we assume m ≠ h_n, they also differ in index h_n-/
by_cases hi : m < h_n,
-- m < h_n
{split, --split list.modify goal into a goal for each field
 swap 3,-- swap order of goals, so we can fix n first

 -- FIELD n
{exact (h_n - 1)}, -- as said before, the index is one before h_n

-- FIELD heq
{rw remove_nth_remove_nth, --(see list.lemmas.long_lemmas)
 split_ifs with ite1, --split if-then-else into cases
 /- if-case (named ite1): m < h_n - 1 + 1
    => first goal : remove_nth (remove_nth L1 (h_n - 1 + 1)) m = remove_nth (remove_nth L2 m) (h_n - 1)-/
    {rw nat.sub_add_cancel, -- h_n - 1 + 1 = h_n, if 1 ≤ h_n
      rw h_heq,
      rw remove_nth_remove_nth,
      split_ifs with ite2,
      /- if-case (named ite2): h_n < m + 1
        contradicts hi : m < h_n-/
      exfalso,
      exact nat.lt_le_antisymm ite2 hi, -- a < b and b ≤ a together imply false
      /- else-case (named ite2): ¬ (h_n < m + 1)-/
      refl, -- solves new first goal : remove_nth (remove_nth L2 m) (h_n - 1) = remove_nth (remove_nth L2 m) (h_n - 1)
      exact le_of_lt h_hb, -- gives h_n ≤ length L2, necessary first assumption for second remove_nth_remove_nth
      --new first goal : m + 1 ≤ length L2 (second necessary assumption for second remove_nt_remove_nth)
      rw ← hlength,
      exact hm, -- m < length L1 is definitionally equivalent to m + 1 ≤ length L1 
      exact nat.one_le_of_lt hi,  },-- assumption needed for nat.sub_add_cancel, because 0-1 = 0 in ℕ 
  /- else-case (named ite1): ¬ (m < h_n - 1 + 1)
    contradicts hi-/
    {
      exfalso, 
    rw nat.sub_add_cancel at ite1,
    exact false.elim (ite1 hi),
    exact nat.one_le_of_lt hi,
      },
    
    {exact le_of_lt hm, },/- lemma says : for all a,b of the same type, a < b implies a ≤ b
                             line proves first necessary assumtion for first remove_nt_remove_nth-/

    --prove second necessary assumption for first remove_nt_remove_nth                          
    {rw nat.sub_add_cancel,
    exact le_of_lt h_ha,
    exact nat.one_le_of_lt hi,}, -- assumption needed for nat.sub_add_cancel
    },

-- FIELD bound    
{have p2 : h_n-1 < h_n, /- will be needed in line 276/277 (proving it here makes this
                           hypothesis hold universally inside these {}-brackets)-/
   cases h_n,
     -- h_n = 0
     exfalso, -- contradicts hi as m ∈ ℕ 
     exact nat.not_succ_le_zero m hi,
   -- nat.succ h_n
   exact lt_add_one (nat.succ h_n - 1), -- lemma says: for all a, a < a + 1 
 rw nth_le_remove_nth, --(see list.lemmas.long_lemmas)
 rw nth_le_remove_nth,
 split_ifs with ite, --split if-then-else into cases
    /- if-case (named ite): m ≤ h_n - 1
        => first goal : abs (nth_le L1 (h_n - 1 + 1) ?m_1 - nth_le L2 (h_n - 1 + 1) ?m_2) ≤ d
        That is true by h_bound and as h_n - 1 + 1 = h_n-/
    convert h_bound using 1,
    have x : h_n - 1 + 1 = h_n,
      apply nat.sub_add_cancel,
      exact nat.one_le_of_lt hi,
    simp only [x], /- simp only because proofs of existence of indices for nth_le 
                      need to be rewritten at the same time -/ 

    -- proofs of some necessary hypotheses through convert
    rw nat.sub_add_cancel,
    exact h_ha,
    exact nat.one_le_of_lt hi,
    rw ← hlength,
    rw nat.sub_add_cancel,
    exact h_ha,
    exact nat.one_le_of_lt hi,
 /- else-case (named ite): ¬ (m ≤ h_n - 1)
    contradicts hi-/
 exfalso,
 have p : m ≤ h_n -1,
   exact nat.le_pred_of_lt hi, -- lemma says : forall m,n in ℕ, if m < n, then m ≤ n - 1
 exact false.elim (ite p),
 
 -- proof of some necessary hypotheses from nth_le_remove_nth
 exact lt.trans p2 h_hb,
 exact lt.trans p2 h_ha,
 
 },

 -- FIELD ha
{rw length_remove_nth, 
 cases h_n,
  --h_n = 0
   exfalso,
   exact nat.not_succ_le_zero m hi,
 -- nat.succ h_n
 rw nat.succ_eq_add_one,
 rw nat.add_sub_cancel,
 exact nat.lt_pred_iff.mpr h_ha, -- lemma says: for all n, m in ℕ, n < pred m ↔ succ n < m 
 exact hm,
},

-- FIELD hb
{rw length_remove_nth, 
 rw ← hlength,
 cases h_n,
   --h_n = 0
   exfalso,
   exact nat.not_succ_le_zero m hi,
 -- nat.succ h_n
 rw nat.succ_eq_add_one,
 rw nat.add_sub_cancel,
 exact nat.lt_pred_iff.mpr h_ha,
 rw ← hlength,
 exact hm,
 },},

-----------------------------------------------------------------------------

 -- hi becomes ¬ (m < h_n)
{have hx : h_n < m, -- because of hi and our initial assumption that m ≠ h_n
   push_neg at hi,
   exact lt_of_le_of_ne hi (ne.symm h_neq),

 split, --split list.modify goal into a goal for each field
 swap 3, -- swap order of goals, so we can fix n first

-- FIELD n
{exact h_n}, /- now we remove an element after h_n, so the position
                of h_n does not change in relation to the beginning of the list-/

-- FIELD heq
{rw remove_nth_remove_nth,
 split_ifs with ite1, --split if-then-else into cases
 /- if-case (named ite1): m < h_n + 1
    contradicts hx-/
 {exfalso, 
  exact nat.lt_le_antisymm ite1 hx,
  },
  /- else-case (named ite1): ¬ (m ≤ h_n + 1)
    => first goal : remove_nth (remove_nth L1 h_n) (m - 1) = 
                    remove_nth (remove_nth L2 m) h_n
    True by h_heq and changing order of element removal again-/
 {rw h_heq,
 rw remove_nth_remove_nth,
 split_ifs with ite2,
   /- if-case (named ite2): h_n < m - 1 + 1
      => first goal : remove_nth (remove_nth L2 (m - 1 + 1)) h_n = 
                      remove_nth (remove_nth L2 m) h_n
    True as 1 ≤ m because of hx abd h_n being a natural number-/
  {rw nat.sub_add_cancel,
  exact nat.one_le_of_lt hx}, -- proves necessary hypothesis for nat.sub_add_cancel
   /- else-case (named ite1): ¬ (h_n < m - 1 + 1)
    contradicts hx-/
  {exfalso,
  rw nat.sub_add_cancel at ite2,
  exact false.elim (ite2 hx),
  exact nat.one_le_of_lt hx, -- proves necessary hypothesis for nat.sub_add_cancel
 }, 
 -- prove necessary hypotheses for remove_nth_remove_nth
 exact le_of_lt h_hb,
 rw ← hlength,
 rw nat.sub_add_cancel,
 exact le_of_lt hm,
 exact nat.one_le_of_lt hx,
 },
 exact le_of_lt hm,
 exact h_ha,},

 -- FIELD bound
 /- true because the h_n-th element of (remove_nth L1 m) is also 
    the h_n-th element of L1 (similarly for L2)-/
  {rw nth_le_remove_nth, 
 rw nth_le_remove_nth,
 split_ifs with ite, --split if-then-else into cases
  /- if-case (named ite): m ≤ h_n - 1
     contradicts hx-/
   exfalso,
   exact nat.lt_le_antisymm hx ite,
  /- else-case (named ite): ¬ (m ≤ h_n)
      => first goal : abs (nth_le L1 h_n ?m_1 - nth_le L2 h_n ?m_2) ≤ d
     That is just h_bound-/
 convert h_bound using 1,
-- prove necessary hypotheses for remove_nth_remove_nth
 rw ← hlength,
 exact lt_of_le_of_lt hx hm,
 exact lt_of_le_of_lt hx hm,},

-- FIELD ha
{rw length_remove_nth, /- lemma says, if n < length L , then length (remove_nth L n) = length L - 1
                                      for any list L, natural number n -/ 
   have p2 : m ≤ length L1 - 1,
     exact nat.le_pred_of_lt hm,
   exact lt_of_lt_of_le hx p2,
 
   exact hm, --necessary hypothesis for length_remove_nth
},

-- FIELD hb
{rw length_remove_nth, 
 rw ← hlength,
 have p2 : m ≤ length L1 - 1,
    exact nat.le_pred_of_lt hm,
 exact lt_of_lt_of_le hx p2,
 --necessary hypothesis for length_remove_nth
 rw ← hlength,
 exact hm, 
 },},

end


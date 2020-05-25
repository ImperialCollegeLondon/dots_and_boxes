import data.list.basic tactic.linarith
import sle.lemmas


open list

-- changing one element of a list by at most d
/--Two lists that are equal except one entry differs by at most d-/
structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d)



/--Two lists that are equal except one entry differs by at most d have equal length-/
theorem list.modify_refl {L : list ℤ } {d : ℤ} (h : 0 < length L) (p : 0 ≤ d): list.modify L L d :=
{ n := 0,
  ha := h,
  hb := h,
  heq := by refl,
  bound := begin 
           cases L, 
           exfalso, 
           exact nat.not_succ_le_zero 0 h,
           rw nth_le, 
           simp only [abs_zero, add_right_neg, sub_eq_add_neg],
           exact p,
           end
}

theorem eq_size_of_modify_list {l1 l2 : list ℤ } {d : ℤ} (h : list.modify l1 l2 d) : l1.length = l2.length :=
begin
  -- split list.modify condition into its statements
  cases h, 
  -- as the lists below are equal by h_heq, their length must be equal
  have P : length(remove_nth l1 h_n) = length(remove_nth l2 h_n), 
  rw h_heq, 
  rw length_remove_nth l1 h_n h_ha at P, 
  rw length_remove_nth l2 h_n h_hb at P,  
  --need this for finish to work
  have Q : ¬ h_n < 0, simp,
  -- Now  P gives the result by cancelling -1 on both sides, but this
  -- only works if both lists have length > 0. Hence split into easy cases 
  -- and let Lean do the rest
  cases l1, dsimp at h_ha,
  exfalso, finish,
  cases l2, dsimp at h_hb,
  exfalso, finish, 
  finish, 
  end


/--Two lists that are equal except one entry differs by at most d are element
wise equal in all entries except the one at which they differ-/
theorem list.modify_same {A : list ℤ} {B : list ℤ} {d : ℤ}
  (h : list.modify A B d) (m : ℕ) (hmA : m < A.length) (hmB : m < B.length)
  (hmn : h.n ≠ m) : A.nth_le m hmA = B.nth_le m hmB :=
begin
  have H : length A = length B, exact eq_size_of_modify_list h,
  cases h, rw remove_nth_eq_nth_tail at h_heq, rw modify_nth_tail_eq_take_drop at h_heq,
  rw remove_nth_eq_nth_tail at h_heq, rw modify_nth_tail_eq_take_drop at h_heq,
  have p : length (tail (drop h_n A)) = length (tail (drop h_n B)), rw length_tail,
  rw length_tail, rw length_drop, rw length_drop,
  rw H, 
  have h_eq_left : take h_n A = take h_n B , exact append_inj_right' h_heq p,
  have h_eq_right : tail (drop h_n A) = tail (drop h_n B), exact append_inj_left' h_heq p,
  
  rw ← head_reverse_take, rw ← head_reverse_take, 

  have m_cases : (m+1) ≤ h_n ∨ h_n < (m+1) , exact le_or_lt (m + 1) h_n,
  cases m_cases, 
  rw take_lemma m_cases h_eq_left,

  rw nat.lt_iff_add_one_le at hmA, simp at hmn,
  have h1 : 1 ≤ m,
  cases m,
  exfalso,
  have hn_0 : h_n = 0, rw nat.lt_add_one_iff at m_cases,
  exact nat.eq_zero_of_le_zero m_cases,
  exact false.elim (hmn hn_0),
  exact dec_trivial,
  rw take_drop_head_eq h1 hmA,
  clear hmB,
  have hmB: m + 1 ≤ length B, rw ←  H, exact hmA,
  rw take_drop_head_eq h1 hmB,
  have P : tail (drop (m - 1) A) = tail (drop (m - 1) B),
  {
   rw tail_drop,
   rw tail_drop,
   rw tail_drop at h_eq_right,
   rw tail_drop at h_eq_right,
   have h2 : nat.succ h_n ≤ nat.succ (m-1),
   rw nat.succ_le_succ_iff,
   rw nat.lt_add_one_iff at m_cases,
   apply nat.le_pred_of_lt,
   exact lt_of_le_of_ne' m_cases hmn, 

   exact drop_lemma h2 h_eq_right,
  },
  rw P,

  refl,refl,

  
end


/--list.modify is symmetric-/
def list.modify.symm (A B : list ℤ) (d : ℤ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  bound := by rw [←neg_sub, abs_neg]; exact m.bound
}


def list.modify_remove_nth {L1 : list ℤ} {L2 : list ℤ} {d : ℤ}
  (h : list.modify L1 L2 d)  (m : ℕ) (h_neq : m ≠ h.n):
  list.modify (remove_nth L1 m) (remove_nth L2 m) d:=
begin
by_cases hm : m < length L1,
swap,
{push_neg at hm,
 have x1 : remove_nth L1 m = L1,
 exact remove_nth_large_n L1 hm,
 rw x1,
 rw (eq_size_of_modify_list h) at hm,
 have x2 : remove_nth L2 m = L2,
 exact remove_nth_large_n L2 hm,
 rw x2,
 exact h,
},
have hlength : length L1 = length L2,
exact eq_size_of_modify_list h,
cases h,
by_cases hi : m < h_n,
{split, swap 3,
{exact (h_n - 1)},
{rw remove_nth_remove_nth,
 split_ifs,
 {rw nat.sub_add_cancel,
  rw h_heq,
  rw remove_nth_remove_nth,
  split_ifs,exfalso,
  exact nat.lt_le_antisymm h_1 hi,
  refl,
  exact le_of_lt h_hb,
  rw ← hlength,
  exact hm,
  exact nat.one_le_of_lt hi,},
 {
   exfalso, 
 rw nat.sub_add_cancel at h,
 exact false.elim (h hi),
 exact nat.one_le_of_lt hi,
  },
 {exact le_of_lt hm,},
 {rw nat.sub_add_cancel,
 exact le_of_lt h_ha,
 exact nat.one_le_of_lt hi,},
 },
{have p2 : h_n-1 < h_n,
 cases h_n,
 exfalso,
 exact nat.not_succ_le_zero m hi,
 exact lt_add_one (nat.succ h_n - 1),
 rw nth_le_remove_nth, 
 rw nth_le_remove_nth,
 split_ifs,
 convert h_bound using 1,
 have x : h_n - 1 + 1 = h_n,
  apply nat.sub_add_cancel,
  exact nat.one_le_of_lt hi,
 simp only [x],
 rw nat.sub_add_cancel,
 exact h_ha,
 exact nat.one_le_of_lt hi,
 rw ← hlength,
 rw nat.sub_add_cancel,
 exact h_ha,
 exact nat.one_le_of_lt hi,
 exfalso,
 have p : m ≤ h_n -1,
 exact nat.le_pred_of_lt hi,
 exact false.elim (h p),
 
 
 exact lt.trans p2 h_hb,
 exact lt.trans p2 h_ha,
 
 },
{rw length_remove_nth, 
 cases h_n,
 exfalso,
 exact nat.not_succ_le_zero m hi,
 rw nat.succ_eq_add_one,
 rw nat.add_sub_cancel,
 exact nat.lt_pred_iff.mpr h_ha,
 exact hm,
},

{rw length_remove_nth, 
 rw ← hlength,
 cases h_n,
 exfalso,
 exact nat.not_succ_le_zero m hi,
 rw nat.succ_eq_add_one,
 rw nat.add_sub_cancel,
 exact nat.lt_pred_iff.mpr h_ha,
 rw ← hlength,
 exact hm,
 },},
{have hx : h_n < m,
  push_neg at hi,
  exact lt_of_le_of_ne hi (ne.symm h_neq),
  split,swap 3,
{exact h_n},
{rw remove_nth_remove_nth,
 split_ifs,
 {exfalso, 
  exact nat.lt_le_antisymm h hx,
  },
 {rw h_heq,
 rw remove_nth_remove_nth,
 split_ifs,
  {rw nat.sub_add_cancel,
  exact nat.one_le_of_lt hx},
  {exfalso,
  rw nat.sub_add_cancel at h_1,
  exact false.elim (h_1 hx),
  exact nat.one_le_of_lt hx,
 }, 
 exact le_of_lt h_hb,
 rw ← hlength,
 rw nat.sub_add_cancel,
 exact le_of_lt hm,
 exact nat.one_le_of_lt hx,
 


 },
 exact le_of_lt hm,
 exact h_ha,},
  {rw nth_le_remove_nth, 
 rw nth_le_remove_nth,
 split_ifs,
 exfalso,
 exact nat.lt_le_antisymm hx h,
 convert h_bound using 1,
 rw ← hlength,
 exact lt_of_le_of_lt hx hm,
 exact lt_of_le_of_lt hx hm,},
  {rw length_remove_nth,
   have p2 : m ≤ length L1 - 1,
    exact nat.le_pred_of_lt hm,
   exact lt_of_lt_of_le hx p2,
 
   exact hm,
},

{rw length_remove_nth, 
 rw ← hlength,
 have p2 : m ≤ length L1 - 1,
    exact nat.le_pred_of_lt hm,
 exact lt_of_lt_of_le hx p2,
 rw ← hlength,
 exact hm,
 },},

end
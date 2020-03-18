import data.multiset
import order.bounded_lattice
import data.finset
import extended_N_le tactic.ring
import init.algebra.functions
import data.int.basic
import logic.basic
import Dotsandboxes_Part1
import Dotsandboxes_2

open nat 
open multiset


lemma cv_rem_chain_no_loops_ge_tb (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → cv (rem_chain_from_sle G a) ≥ tb (rem_chain_from_sle G a) :=
begin
intros x y, unfold cv, show  ↑(tb (rem_chain_from_sle G a)) ≤ fcv (rem_chain_from_sle G a) + ↑(tb (rem_chain_from_sle G a)), 
have h : fcv (rem_chain_from_sle G a) ≥ 0, exact (rem_chain_no_loops_fcv_pos G a x y),
exact int_le_add (↑(tb (rem_chain_from_sle G a))) (fcv (rem_chain_from_sle G a)) h, 
end

lemma tb_ge_2_for_1r (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G  → (2 : ℤ) ≤  ↑(tb (rem_chain_from_sle G a)) :=
begin 
intros x y z, rw z, unfold tb, rw x.right, simp, split_ifs, 
exfalso, have e : G.chains = 0, exact (zero_size G h).left, rw e at y, finish,
exact dec_trivial,
end


--set_option pp.all true
lemma two_point_two_1r {G : sle} {a : nat} : (2 ≤ cv G ) → ( 2 ≤ card (G.chains)) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G → cv (rem_chain_from_sle G a) ≥ 2:=
begin
intros x y H Ha P,
exact le_trans  (tb_ge_2_for_1r G a H Ha P  ) (cv_rem_chain_no_loops_ge_tb G a H Ha),
end

lemma rem_loop_ge_8_fcv_pos (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  → a ∈ G.loops → fcv (rem_loop_from_sle G a) ≥ 0 :=
begin
  intros x y, rw fcv_rem_loop G a y, simp, rw card_rem_c G.loops a y, 
  rw sum_rem_c G.loops a y,
  have H := x.1,
  have H1 := x.2,
  clear x,
  have H2 := filter_eq_self.1 H.symm,
  have H3 := exists_cons_of_mem y,
  cases H3 with t Ht,
  rw Ht,
  rw sum_cons,
  rw card_cons,
  rw nat.add_sub_cancel,
  rw nat.add_sub_cancel_left,
  rw ←sub_eq_add_neg,
  show (0 : ℤ) ≤ _,
  rw H,
  sorry

end


lemma cv_rem_loop_ge_8_ge_tb (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  → a ∈ G.loops → cv (rem_loop_from_sle G a) ≥ tb (rem_loop_from_sle G a) :=
begin
intros x y, unfold cv, show  ↑(tb (rem_loop_from_sle G a)) ≤ fcv (rem_loop_from_sle G a) + ↑(tb (rem_loop_from_sle G a)), 
have h : fcv (rem_loop_from_sle G a) ≥ 0, exact (rem_loop_ge_8_fcv_pos G a x y),
exact int_le_add (↑(tb (rem_loop_from_sle G a))) (fcv (rem_loop_from_sle G a)) h, 
end

lemma mem_chain_nonzero {G : sle} {a : nat} : a ∈ G.chains → size G ≠ 0 := 
begin 
intro x, 
have h : ∃ t, G.chains = a :: t, exact exists_cons_of_mem x, cases h with t ht, 
dunfold size, rw ht, simp, rw add_comm, exact succ_ne_zero _, 
end

lemma mem_loop_nonzero {G : sle} {a : nat}: a ∈ G.loops → size G ≠ 0 := 
begin 
intro x, 
have h : ∃ t, G.loops = a :: t, exact exists_cons_of_mem x, cases h with t ht, 
dunfold size, rw ht, simp, rw add_comm, exact succ_ne_zero _, 
end

lemma tb_ge_4_for_2r (G : sle) (a : nat) : a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G  → (4 : ℤ) ≤  ↑(tb (rem_loop_from_sle G a)) :=
begin 
intros   y z, rw z, unfold tb, have h : size G ≠ 0, exact mem_loop_nonzero y, split_ifs, exfalso, exact false.elim (h h_1),
repeat {exact dec_trivial}, 
end

lemma two_point_two_2r {G : sle} {a : nat} :  
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G → cv (rem_loop_from_sle G a) ≥ 4:=
begin
intros H Ha P,
exact le_trans  (tb_ge_4_for_2r G a Ha P  ) (cv_rem_loop_ge_8_ge_tb G a H Ha),
end



lemma cv_rem_loop_ge_8_three_chain_fcv_pos (G : sle) (a : nat) : (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)  → a ∈ G.loops → fcv (rem_loop_from_sle G a) ≥ 0 :=
begin 
intros x y, rw fcv_rem_loop G a y, rw x.left, simp, sorry
end

lemma cv_rem_loop_ge_8_three_chain_ge_tb (G : sle) (a : nat) : (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) → a ∈ G.loops → cv (rem_loop_from_sle G a) ≥ tb (rem_loop_from_sle G a) :=
begin
intros x y, unfold cv, show  ↑(tb (rem_loop_from_sle G a)) ≤ fcv (rem_loop_from_sle G a) + ↑(tb (rem_loop_from_sle G a)), 
have h : fcv (rem_loop_from_sle G a) ≥ 0, exact (cv_rem_loop_ge_8_three_chain_fcv_pos G a x y),
exact int_le_add (↑(tb (rem_loop_from_sle G a))) (fcv (rem_loop_from_sle G a)) h, 
end

lemma two_point_two_3r {G : sle} {a : nat} : 
(G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G → cv (rem_loop_from_sle G a) ≥ 4:=
begin
intros H Ha P,
exact le_trans  (tb_ge_4_for_2r G a Ha P  ) (cv_rem_loop_ge_8_three_chain_ge_tb G a H Ha),
end









theorem two_point_two_ad (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3::0)) 
∧ (card (G.loops) = 1)) → (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))) :=
begin
intros x y z, have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, exfalso, exact false.elim (z H),
cases H, left, dunfold size at y, rw H.right at y, simp at y, have P : 0 < card G.chains, have K : 2 ≤ card (G.chains), exact y,
rw le_iff_eq_or_lt at K, cases K, rw ← K, exact dec_trivial, exact lt_trans (dec_trivial) K, rw card_pos_iff_exists_mem at P, cases P with a Ha,
have T : tb (rem_chain_from_sle G a) = tb G , 
exact two_point_two_1 G a y H Ha,----------------------------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T, exact two_point_two_1r x y H Ha T,----------------------oooooooooooo
cases H,  right, have L : G.loops ≠ 0, finish, 
have LL : ∃ (a : ℕ), a ∈ G.loops, exact exists_mem_of_ne_zero L, cases LL with a Ha, 
have T : tb (rem_loop_from_sle G a) = tb G ,  
exact two_point_two_2 G a y z H Ha,--------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T, exact two_point_two_2r H Ha T,--------oooooo
cases H,  right, 
have LL : ∃ (a : ℕ), a ∈ G.loops, have n :  G.loops ≠ 0, simp, intro m, dunfold size at y, rw [m, H.left] at y, 
have Q : ¬ 1 ≥ 2, exact dec_trivial, finish, exact exists_mem_of_ne_zero n , cases LL with a Ha, 
have T : tb (rem_loop_from_sle G a) = tb G,  
exact two_point_two_3 G a y z H Ha,------------------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T,  exact two_point_two_3r H Ha T,-------oooooooooooooo
cases H, have Hl: 3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops ,  exact H.left,
cases Hl, left, 
have T : tb (rem_chain_from_sle G 3) = tb G ,
exact two_point_two_4_1 G y z H.right Hl,------------------------
fapply exists.intro, exact 3, fapply exists.intro, exact Hl, 
split, exact T, exact le_trans ( dec_trivial ) (rem_three_chain_to_cb_ge_3 G x Hl T), -------------ooooooooooooooooo
cases Hl, right, 
have T : tb (rem_loop_from_sle G 4) = tb G , 
  exact two_point_two_4_2 G y z H.right Hl,-----------------
fapply exists.intro, exact 4, fapply exists.intro, exact Hl,split, exact T, exact le_trans ( dec_trivial ) (rem_four_loop_to_cb_ge_4 G x Hl T),----------------oooooooooooooooooooooo
right, 
have T : tb (rem_loop_from_sle G 6) = tb G , 
 exact two_point_two_4_3 G y z H.right Hl,--------------------
fapply exists.intro, exact 6, fapply exists.intro, exact Hl,split, exact T, exact le_trans ( dec_trivial ) (rem_six_loop_to_cb_ge_4 G x Hl T),-------ooooooooooooooooooooo
cases H, left,
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0,-- rw ← h_3 at d, rw mem_erase_dup at d, 
rw ← H.right at d, rw mem_erase_dup at d,  
have T : tb (rem_chain_from_sle G 3) = tb G ,
  exact two_point_two_5 G y z H d,---------------
fapply exists.intro, exact 3, fapply exists.intro, exact d,split, exact T, exact le_trans ( dec_trivial ) (rem_three_chain_to_cb_ge_3 G x d T),-------ooooooooooooooooooooooooooooo
cases H, right, have Hl: 4 ∈ G.loops ∨ 6 ∈ G.loops , exact H.left,
cases Hl, have T : tb (rem_loop_from_sle G 4) = tb G , 
 exact two_point_two_6_1 G y z H Hl,--------------------
fapply exists.intro, exact 4, fapply exists.intro, exact Hl, split, exact T,exact le_trans ( dec_trivial ) (rem_four_loop_to_cb_ge_4 G x Hl T),-------------------ooooooooooooooooooooo
have T : tb (rem_loop_from_sle G 6) = tb G, 
 exact two_point_two_6_2 G y z H Hl,--------------------
fapply exists.intro, exact 6, fapply exists.intro, exact Hl, split, exact T, exact le_trans ( dec_trivial ) (rem_six_loop_to_cb_ge_4 G x Hl T),-----------oooooooooooooooooooooooooooooooooo
dunfold size at y, right, have Hl: 4 ∈ G.loops ∨ 6 ∈ G.loops , exact H.left,
cases Hl, have T : tb (rem_loop_from_sle G 4) = tb G, 
exact two_point_two_7_1 G y z H Hl,
fapply exists.intro, exact 4, fapply exists.intro, exact Hl, split, exact T, exact le_trans ( dec_trivial ) (rem_four_loop_to_cb_ge_4 G x Hl T),
have T : tb (rem_loop_from_sle G 6) = tb G , 
 exact two_point_two_7_2 G y z H Hl,
fapply exists.intro, exact 6, fapply exists.intro, exact Hl, split, exact T, exact le_trans ( dec_trivial ) (rem_six_loop_to_cb_ge_4 G x Hl T),
end

lemma empty_of_size_zero (G : sle) : size G = 0 → G = empty_game_sle :=
begin
  intro H0,
  cases G,
  unfold empty_game_sle,
  change multiset.card G_chains + multiset.card G_loops = 0 at H0,
  congr;
    show _ = (0 : multiset ℕ);
    rw ←multiset.card_eq_zero;
    apply nat.eq_zero_of_le_zero;
    rw ←H0,
      exact nat.le_add_right _ _,
      exact nat.le_add_left _ _,
end

lemma chain_or_loop_of_size_pos (G : sle) :
size G > 0 → {c : ℕ // c ∈ G.chains} ⊕ {l : ℕ // l ∈ G.loops} :=
begin
  intro H0,
  change 0 < multiset.card G.chains + multiset.card G.loops at H0,
  by_cases h : card G.chains = 0,
  { rw [h,zero_add,card_pos_iff_exists_mem] at H0,
    right,
    exact ⟨nat.find H0,nat.find_spec H0⟩
  },
  have H0 : 0 < card G.chains := nat.pos_of_ne_zero h,
  rw card_pos_iff_exists_mem at H0,
  left,exact ⟨nat.find H0,nat.find_spec H0⟩
end

lemma succ_rem_chain (G : sle) (c : ℕ) (Hc : c ∈ G.chains) :
size G = size (rem_chain_from_sle G c) + 1 :=
begin
  unfold rem_chain_from_sle,
  dunfold size,
  show card (G.chains) + card (G.loops) = card (erase (G.chains) c) + card (G.loops) + 1,
  rw card_erase_of_mem Hc,
  suffices : nat.pred (card (G.chains)) + 1 = card G.chains,
    conv begin to_lhs,
    rw ←this, end,
    simp,
  apply nat.succ_pred_eq_of_pos,
  show 0 < _,
  rw card_pos_iff_exists_mem,
  existsi c,exact Hc,
end

lemma succ_rem_loop (G : sle) (l : ℕ) (Hl : l ∈ G.loops) :
size G = size (rem_loop_from_sle G l) + 1 :=
begin
  unfold rem_loop_from_sle,
  dunfold size,
  dsimp,
  show card (G.chains) + card (G.loops) = card (G.chains) + card (erase (G.loops) l) + 1,
  rw card_erase_of_mem Hl,
  suffices : nat.pred (card (G.loops)) + 1 = card G.loops,
    conv begin to_lhs,
    rw ←this, end,
    simp,
  apply nat.succ_pred_eq_of_pos,
  show 0 < _,
  rw card_pos_iff_exists_mem,
  existsi l,exact Hl,
end

theorem sle.induction' (p : sle → Sort*)
(H0 : p empty_game_sle)
(Hchain : ∀ (G : sle) (c : ℕ), c ∈ G.chains → p (rem_chain_from_sle G c) → p G)
(Hloop : ∀ (G : sle) (l : ℕ), l ∈ G.loops → p (rem_loop_from_sle G l) → p G) :
∀ G : sle, p G :=
begin
  intro G,
  generalize h : size G = m, -- Simon Hudon's trick for doing induction on size
  revert G h,
  induction m with d Hd,
    intros G HG,
    rwa empty_of_size_zero G HG,
  intros G HG,
  have Htemp := nat.succ_pos d,
  rw ←HG at Htemp,
  have Hcl := chain_or_loop_of_size_pos G Htemp,
  cases Hcl with HC HL,
  { cases HC with c Hc,
    apply Hchain G c Hc,
    apply Hd,
    apply nat.succ.inj,
    show (size (rem_chain_from_sle G c)) + 1 = _,
    rwa ←succ_rem_chain G c Hc,
  },
  { cases HL with l Hl,
    apply Hloop G l Hl,
    apply Hd,
    apply nat.succ.inj,
    show (size (rem_loop_from_sle G l)) + 1 = _,
    rwa ←succ_rem_loop G l Hl,
  }
end


/-
theorem sle.induction_aux (m : ℕ) (p : sle → Sort*)
(H0 : p empty_game_sle)
(Hchain : ∀ (G : sle) (c : ℕ) (Hc : c ≥ 3), p G → p (cons_chain_to_sle G c Hc))
(Hloop : ∀ (G : sle) (l : ℕ) (Hl : l ≥ 4) (Pl : 2 ∣ l), p G → p (cons_loop_to_sle G l Hl Pl)) :
∀ G : sle, size G = m → p G :=
begin
  induction m with d Hd,
    intros G HG,
    rwa empty_of_size_zero G HG,
  
end
/- my proposal for an inductive hypothesis-/
theorem sle.induction (p : sle → Sort*)
(H0 : p empty_game_sle)
(Hchain : ∀ (G : sle) (c : ℕ) (Hc : c ≥ 3), p G → p (cons_chain_to_sle G c Hc))
(Hloop : ∀ (G : sle) (l : ℕ) (Hl : l ≥ 4) (Pl : 2 ∣ l), p G → p (cons_loop_to_sle G l Hl Pl)) :
∀ G : sle, p G := λ G, sle.induction_aux (size G) p H0 Hchain Hloop G rfl

theorem two_point_two_ak_bk_loop_aux (G : sle) (a : nat) (h : a ∈ G.loops) (k : ℕ) :
size G = k → 
(cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) ∧ (multiset.card(G.loops) = 1))
→ (tb (rem_loop_from_sle G a) = tb G) ∧ (cv (rem_loop_from_sle G a) ≥ 4)
→ loop_move_is_optimal G a ∧ (int.of_nat (value G) = cv G) := 
begin
  induction k with d Hd,
  { -- base case
    intros H0 H1 H2,
    rw H0 at H2,
    exfalso,
    revert H2,
    exact dec_trivial,
  },
  intros,
  have H : loop_move_is_optimal G a,
  { sorry

  },
  split,
  exact H,

end

theorem two_point_two_ak_bk_loop (G : sle) (a : nat) (h : a ∈ G.loops) :
(cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) ∧ (multiset.card(G.loops) = 1))
→ (tb (rem_loop_from_sle G a) = tb G) ∧ (cv (rem_loop_from_sle G a) ≥ 4)
→ loop_move_is_optimal G a ∧ (int.of_nat (value G) = cv G) :=
begin
  apply two_point_two_ak_bk_loop_aux G a h (size G),
  refl,
end

-/

lemma value_rem_loop (G : sle) (a : nat) (h: a ∈ G.loops) : int.of_nat (value (rem_loop_from_sle G a)) = ↑(value_aux (G.chains) (erase (G.loops) a)) :=
sorry

lemma cases_size (G : sle): 2 = size G → ∃ (a b : nat), G.chains = a :: b :: 0 ∧ G.loops = 0 ∨ ∃ (a b : nat), G.loops = a :: b :: 0 ∧ G.chains = 0 ∨ ((∃ a, G.chains = a :: 0 )∧ (∃ a, G.loops = a :: 0)):=
sorry

theorem two_point_two_ak_bk_loop (G : sle) (a : nat) (h : a ∈ G.loops) : ¬ ((G.chains = (3 :: 0)) ∧ (multiset.card(G.loops) = 1)) → (2 ≤ cv G) → (2 ≤ size G) →  
 (tb (rem_loop_from_sle G a) = tb G) ∧ (cv (rem_loop_from_sle G a) ≥ 4) → loop_move_is_optimal G a ∧ (int.of_nat (value G) = cv G) :=
begin
  intros ex Hcv, -- random change
  revert a, -- random change
  revert G,
  refine sle.induction' _ _ _ _,
  { -- base case
    intros H1 H2,
    exfalso,
    rw cv_zero at H2,
    revert H2, 
    exact dec_trivial},
  intros G a x y z l m n p q , 
  have H : loop_move_is_optimal G m,
  unfold loop_move_is_optimal,

  sorry,sorry,
   intros  G a x y z l m n p q , 
   have H : loop_move_is_optimal G m,
   unfold loop_move_is_optimal,
   rw ← value_rem_loop G m n,
   rw le_iff_eq_or_lt at p, 
   cases p, 
   have H : ∃ (a b : nat), G.chains = a :: b :: 0 ∧ G.loops = 0 ∨ ∃ (a b : nat), G.loops = a :: b :: 0 ∧ G.chains = 0 ∨ ((∃ a, G.chains = a :: 0 )∧ (∃ a, G.loops = a :: 0)), exact cases_size G p,
   cases H with t Ht,  cases Ht with s Hs, cases Hs,  
  sorry, sorry, sorry, sorry,
end

theorem two_point_two_ak_bk_chain' (G : sle) (a : nat) (h : a ∈ G.chains) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) →  (tb (rem_chain_from_sle G a) = tb G) ∧ (cv (rem_chain_from_sle G a) ≥ 2) → chain_move_is_optimal G a ∧ (int.of_nat (value G) = cv G):=
begin
intros,
 sorry, 
end

theorem two_point_two_ak_bk_loop' (G : sle) (a : nat) (h : a ∈ G.loops) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) →  (tb (rem_loop_from_sle G a) = tb G) ∧ (cv (rem_loop_from_sle G a) ≥ 4) → loop_move_is_optimal G a ∧ (int.of_nat (value G) = cv G) := 
begin
intros x y z n, sorry,
--induction (size G) with t Ht, 
end

/-
lemma three_point_one (G : sle) : (G ≠ empty_game) → (G.chains = filter (λ x, x ≥ 4) G.chains) → (G.loops = filter (λ x, x ≥ 6) G.loops) →  
(value G ≥ 2) := 
begin
intros x y z, unfold value, rw value_aux_eq, 
show  N_min
      (pmap (λ (a : ℕ) (h : a ∈ G.chains), v_of_G_with_chain G a)
           (G.chains)
           _ +
         pmap
           (λ (a : ℕ) (h : a ∈ G.loops), v_of_G_with_loop G a)
           (G.loops)
           _) ≥
    2, 
    rw y
    
  sorry,
end
-/



theorem for_two_point_three (G : sle) : cv G ≥ 2 → size G ≥ 2 → (G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1) → int.of_nat (value G) = cv G :=
begin
intros x y z, have H : ∃ x, G.loops = x :: 0, exact  multiset.card_one_iff_singleton.1 z.right, cases H with a Pa,
show ↑ (value G) = cv G,
rw [ ← loop_and_three_chain_case G a],
have n : a ∈ a :: 0, exact mem_cons_self a 0, rw ← Pa at n, exact (G.loops_are_long_and_even a n).left,
exact z.left,
exact Pa, 
end






theorem two_point_three (G : sle) : cv G ≥ 2 → int.of_nat (value G) = cv G :=
begin 
intro x, have h : (size G) = 0 ∨ (size G) = 1 ∨ ((size G) ≥ 2 ∧ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1))) ∨ ((size G) ≥ 2 ∧ ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1))), exact zero_one_or_ge_2_cond (size G) ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)), cases h,
rw ← empty_game_iff_size_zero at h, rw v_of_empty_game G h, rw h, rw cv_zero, refl, 
cases h, show ↑ (value G) = cv G, exact eq.symm (one_comp_case G h), 
cases h, exact for_two_point_three G x h.left h.right,

 sorry,
--exact two_point_two_ak_bk G x h.left h.right, 
end--by theorems from before


/-

theorem one_point_three (G : simple_loony_endgame) : (value_G G ≥ 3 ) ↔ ((cv_G G ≥ 3) ∨  (((G.three_chains = 0 ∧ squnum_G G = 2 % 4 )
 ∨ (G.three_chains = 1 ∧ squnum_G G = 3 % 5)) ∧ (((cv_G G + 4*G.four_loops < 2) ∧ (G.four_loops = 0 % 2 )) 
 ∨ ((cv_G G + 4*G.four_loops > 2) ∧ ((G.four_loops = 3 % 8) ∨ (G.four_loops = 4 % 8) ∨ (G.four_loops = 5 % 8) ) ) ))) :=
begin
 split, 
 intro x, 
 induction G.three_chains with t Ht, induction G.four_loops with f Hf, simp, 
 sorry, simp, sorry, sorry, sorry
 end

-/


theorem one_point_three_sle (G : sle) : (value G ≥ 3 ) ↔ ((cv G ≥ 3) ∨  (((3 ∉ G.chains ∧ squnum G = 2 % 4 )
 ∨ (count 3 G.chains = 1 ∧ squnum G = 3 % 4)) ∧ (((cv G + 4*(count 4 G.loops) < 2) ∧ (count 4 G.loops = 0 % 2 )) 
 ∨ ((cv G + 4*count 4 G.loops > 2) ∧ ((count 4 G.loops = 3 % 8) ∨ (count 4 G.loops = 4 % 8) ∨ (count 4 G.loops = 5 % 8) ) ) ))) :=
begin
 split, 
 intro x, 
 have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, sorry,
 sorry,
  simp, sorry, 
 end




/-
theorem two_point_two (G : simple_loony_endgame) : (cv_G G ≥ 2) → (size_G G ≥ 2) → ¬ ((G.three_chains = 1) 
∧ (multiset.card(all_loops G) = 1)) → (value G = cv_G G):= sorry-/


theorem three_point_two_1 (G: sle) : ((size G) > 0) → (cv G ≤ 1) → (value G ≤ 4) := 
begin
intros x y, sorry,
end



lemma size_neq_zero_tb_ge_4 (G : sle) : size G ≠ 0 → 4 ≤ tb G :=
begin
intro x, unfold tb, split_ifs, 
exfalso, finish,
exact dec_trivial,
exact dec_trivial,
exact dec_trivial,
exact dec_trivial,
end




lemma aargh (a b : nat) : a ≤ a + b :=
begin induction b with t h, simp, have p : a + t ≤ a + succ t, rw add_succ, exact le_succ (a + t), exact le_trans h p, end  


lemma basic {a b : nat} : a = b ↔ b = a := begin split, intro x, rw x, intro x, rw x, end 

--lemma three_point_two (G: simple_loony_endgame) : ((size_G G) > 0) → (cv_G G < 2) → (value_G G ≤ 4) ∧ ((G.three_chains > 0) ∨
--(G.four_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops ≥ 2 ∧ (size_G G) > 2)) := sorry

theorem three_point_two (G: sle) : (0 < (size G)) → (cv G ≤ 1) → (value G ≤ 4) → ((1 ≤ count 3 G.chains  ∧ 2 ≤ (size G) ) ∨
(1 ≤ count 4 G.loops  ∧ 2 ≤ (size G)) ∨ (2 ≤ count 6 G.loops ∧ 3 ≤ (size G))) := 
begin
intros x y z, dunfold size at x,  
have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, left, rw H.left, simp, split, exact dec_trivial, dunfold size, rw H.left, rw H.right, exact dec_trivial,
cases H, exfalso, unfold cv at y, unfold fcv at y, rw H.right at y, rw H.left at y, simp at y, 
 sorry,
cases H, exfalso, have p : ∃  (n : ℤ) (H : 0 ≤ n ),  cv G =  n + ↑ (tb G) - count 3 G.chains - 4 * count 4 G.loops - 2 * count 6 G.loops,
exact rw_cv G, cases p with t Ht, cases Ht with s Hs,  rw Hs at y, rw H.left at y, rw (H.right).left at y, rw count_filter_eq_zero at y,
rw count_filter_eq_zero at y, rw count_filter_eq_zero at y,  sorry, exact dec_trivial, exact dec_trivial, exact dec_trivial, 
cases H, left, rw H.left, simp, split, exact dec_trivial, dunfold size, rw H.left, simp,
have Q : 0 ≤ card G.loops , exact zero_le (card G.loops), rw le_iff_eq_or_lt at Q, cases Q,
exfalso, rw basic at Q, rw card_eq_zero at Q, unfold cv at y, unfold fcv at y, unfold tb at y, rw [Q, H.left] at y,
simp at y, have h : size G ≠ 0, dunfold size, rw [Q, H.left], simp, split_ifs at y, exact false.elim (h h_1),
have r : ¬ int.of_nat 0 + (int.of_nat 3 + (-4 + ↑4)) < 2, show ¬ (↑0) + (int.of_nat 3 + (-4 + ↑4)) < 2, ring,  sorry,
  exact false.elim (r y), rw add_comm, rw ← succ_eq_add_one, apply succ_le_succ, finish, 
cases H, cases H.left, left, have P : ∃ t, G.chains = 3 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 3 t), cases H.right with n Pn, cases Pn with P N, rw ht at N, rw mem_cons at N,
cases N,  exfalso, rw N at P, have L : ¬ 3 ≥ 4, exact dec_trivial, exact false.elim (L P), 
have B : ∃ s, t = n :: s,exact exists_cons_of_mem N, cases B with s hs, rw hs at ht, dunfold size, rw ht, simp, rw ← add_assoc,
show 2 ≤ 2 + (card s + card (G.loops)), exact aargh 2 (card s + card (G.loops)),
cases h, right, left, have P : ∃ t, G.loops = 4 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 4 t), 
 cases H.right with n Pn, cases Pn with P N, have B : ∃ s, G.chains = n :: s,exact exists_cons_of_mem N, cases B with s hs, dunfold size, rw ht, rw hs, simp,
  rw ← add_assoc, show 2 ≤ 2 + (card t + card s), exact aargh 2 (card t + card s),
right, right,  have P : ∃ t, G.loops = 6 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp,  sorry, sorry, 
cases H, left, split, sorry,
have P : card (G.chains) ≥ 2, exact count_imp_card H.left, dunfold size, sorry,
cases H, cases H.left, right, left, have P : ∃ t, G.loops = 4 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 4 t), sorry,
right, have q : 4 ∈ G.loops ∨ ¬ 4 ∈ G.loops, exact dec_em (4 ∈ G.loops), 
cases q, left, have w : ∃ t, G.loops = 4 :: t, exact exists_cons_of_mem q, cases w with t Ht,rw Ht,  split,
simp, rw succ_eq_add_one, simp, exact zero_le (count 4 t),
rw Ht at h, rw mem_cons at h, cases h, exfalso, finish,  have v : ∃ a, t = 6 :: a,   exact exists_cons_of_mem h, cases v with s Hs, rw Hs at Ht,
dunfold size, rw [Ht, H.right ], simp, rw ← add_assoc, show 2 ≤ 2 + card s, exact aargh 2 (card s),sorry, sorry,
end

lemma three_point_two_f1 (G : sle) : ((size G) > 0) → (cv G ≤ 1) → 3 ∈ G.chains → value G ≤ 3 ∧ value (rem_chain_from_sle G 3) ≤ 4:=
begin
intros x y z, split, 
sorry, sorry,
end

lemma three_point_two_f2 (G : sle) : ((size G) > 0) → (cv G ≤ 1) → 4 ∈ G.loops → value (rem_loop_from_sle G 4) ≤ 5 :=
begin 
intros x y z, sorry
end

lemma three_point_two_f3 (G : sle) : ((size G) > 0) → (cv G ≤ 1) → ¬ 3 ∈ G.chains → ¬ 4 ∈ G.loops → value (rem_loop_from_sle G 6) ≤ 4  :=
sorry

theorem three_point_two_f (G: sle) : ((size G) > 0) → (cv G ≤  1) → if mem 3 G.chains then value G ≤ 3 ∧ value (rem_chain_from_sle G 3) ≤ 4 
else if mem 4 G.loops then value (rem_loop_from_sle G 4) ≤ 5 else  value (rem_loop_from_sle G 6) ≤ 4 := 
begin
intros x y, split_ifs, exact three_point_two_f1 G x y h, exact three_point_two_f2 G x y h_1, exact three_point_two_f3 G x y h h_1, 
end

theorem three_point_three (G : sle) : G_is_even G → 
if size G = 0 then value G = 0
else if cv G ≥ 3 then int.of_nat (value G) = cv G
else if cv G = 0 ∧ 3 ∈ G.chains ∧ 4 ∈ G.loops ∧ ((∃ c ∈ G.chains, c ≥ 4) ∨ (∃ c ∈ (rem_loop_from_sle G 4).loops, c ≥ 4)) then value G = 0
else if cv G < 2 ∧ 4 ∣ (cv G) ∧ 3 ∉ G.chains ∧ cv G + 4 * (count 4 G.loops) < 2 then value G = (if 2 ∣ count 4 G.loops then 4 else 0)
else if cv G < 2 ∧ 4 ∣ (cv G) ∧ 3 ∉ G.chains ∧ cv G + 4 * (count 4 G.loops) > 2 then value G = (if cv G % 8 = 0 then 0 else 4)
else value G = 2 := 
begin
intro x, split_ifs, rw ← empty_game_iff_size_zero at h, 
exact v_of_empty_game G h, 
have q : 2 ≤ cv G, exact le_trans (dec_trivial) h_1, exact two_point_three G q,

sorry,

sorry,
sorry,
sorry,
sorry,
sorry,

end


--nat.mod_two_eq_zero_or_one


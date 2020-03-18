import data.multiset
import order.bounded_lattice
import data.finset
import extended_N_le tactic.ring
import init.algebra.functions
import data.int.basic
import logic.basic
import Dotsandboxes_Part1

open nat 
open multiset
------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------- functions on multisets ----------------------------------------------------------
theorem filter_inclusion_exclusion (α : Type*) (p q : α → Prop)
  [decidable_pred p] [decidable_pred q] (L : multiset α) :
  filter p L + filter q L = filter (λ x, p x ∨ q x) L + filter (λ x, p x ∧ q x) L :=
multiset.induction_on L (by simp) $ λ hd tl ih,
by by_cases H1 : p hd; by_cases H2 : q hd; simpa [H1, H2] using ih

lemma looplemma (L : multiset ℕ) (H : ∀ l ∈ L, l = 4 ∨ l = 6 ∨ l ≥ 8) :
L = filter (λ l, l = 4) L + filter (λ l, l = 6) L + filter (λ l, l ≥ 8) L :=
have H1 : filter (λ (x : ℕ), x = 4 ∧ x = 6) L = 0,
  from filter_eq_nil.2 $ λ _ _ H, by cc,
have H2 : filter (λ (x : ℕ), (x = 4 ∨ x = 6) ∧ x ≥ 8) L = 0,
  from filter_eq_nil.2 $ λ _ _ H, by cases H.1; subst h;
  from absurd H.2 dec_trivial,
by rw [filter_inclusion_exclusion, H1, add_zero];
rw [filter_inclusion_exclusion, H2, add_zero];
symmetry; rw [filter_eq_self]; intros;
rw [or_assoc]; solve_by_elim

theorem count_filter_eq_zero (α : Type*) (M : multiset α) (p : α → Prop)
(a : α) [decidable_eq α] [decidable_pred p]
(hnp : ¬ p a) : count a (filter p M) = 0 :=
begin
  rw count_eq_zero,
  intro Hin,
  rw mem_filter at Hin,
  apply hnp,
  exact Hin.right
end

example {α : Type*} (L : multiset α) (p : α → Prop) (q : α → Prop)
[decidable_pred p] [decidable_pred q] :
filter p (filter q L) = filter (λ a, p a ∧ q a) L :=
begin
  rw ←filter_map_eq_filter q,
  rw filter_filter_map,
  rw ←filter_map_eq_filter,
  congr,
  funext,
  unfold option.filter,
  unfold option.guard,
  split_ifs;unfold option.bind; try {unfold option.guard;split_ifs},
  finish,cc,finish,refl,finish,
end

theorem filter_congr (α : Type*) (p q : α → Prop) (L : multiset α) (H : ∀ l ∈ L, p l ↔ q l)
[decidable_pred p] [decidable_pred q] :
filter p L = filter q L :=
le_antisymm
  (le_filter.2 ⟨filter_le _,λ a Ha, by rw mem_filter at Ha;exact (H a Ha.1).1 Ha.2⟩)
  (le_filter.2 ⟨filter_le _,λ a Ha, by rw mem_filter at Ha;exact (H a Ha.1).2 Ha.2⟩)


lemma zero_one_or_ge_2_cond (n : ℕ) (p : Prop) : n = 0 ∨ n = 1 ∨ (n ≥ 2 ∧ p) ∨ (n ≥ 2 ∧ ¬ p) :=
begin
  cases n with d,
    left,refl,
  cases d with d,
    right,left,refl,
  cases classical.em p,
    right,right,left,
    split,
    exact dec_trivial,
    assumption,
  right,right,right,
  split,
  exact dec_trivial,
  assumption
end
--lemma v_rem_loop (G : sle) (a : nat) : value (rem_loop_from_sle G a) =  := sorry

--lemma v_rem_chain (G : sle) (a : nat) : value (rem_chain_from_sle G a) =  := sorry


lemma empty_game_iff_size_zero (G : sle) : G = empty_game_sle ↔ size G = 0 :=
begin
split, 
intro x, rw x, dunfold size, unfold empty_game_sle, simp, 
intro x, unfold empty_game_sle, show G =
    {chains := 0,
     chains_are_long := empty_game_sle._proof_1,
     loops := 0,
     loops_are_long_and_even := empty_game_sle._proof_2},
have y : G.chains = 0 ∧ G.loops = 0, exact zero_size G x, 
  cases G, simp at y, cases y with a b, congr',  
end







lemma le_of_sub_le_sub_left_iff (m n k : nat) (Hn : m ≥ n) (Hk : m ≥ k) : m - n ≤  m - k ↔ k ≤ n :=
nat.sub_le_sub_left_iff Hk


lemma loop_and_three_chain_case (G : sle) (n : nat) (Hn : n ≥ 4): G.chains = cons 3 0  → (G.loops =cons n 0 ) 
→ (cv G = value G) := 
begin
 intros a b,
unfold cv, unfold value, unfold tb, unfold fcv,
split_ifs, 
exfalso, dunfold size at h, rw b at h, simp at h, by exact false.elim ((pos_add_pos 1 (card (G.chains)) one_not_zero h )), 
exfalso, rw [← card_eq_zero] at h_1, finish,
exfalso, have p :  cons 3 0 ≠ 0,  exact cons_ne_zero,  exact false.elim ((eq_neq_mult G.chains (cons 3 0) 0 a p) h_2),
rw b, rw [ a, card_cons 3 0, card_zero, card_cons n 0, card_zero] , 
simp, show int.of_nat n - 3 = ↑(value_aux (3 :: 0) (n :: 0)),rw value_aux_eq, rw pmap_cons, rw pmap_cons, simp, rw value_aux_eq,
rw value_aux_eq, simp, unfold N_min, simp, unfold option_N_min, simp, ring, unfold min, split_ifs, unfold dots_and_boxes.option_N_to_N,
show int.of_nat n - 3 = ↑(n - 4 + 4 - 3 - 1 + 1),  rw [ nat.sub_add_cancel], rw nat.sub_add_cancel, have h3 : n ≥ 3 := le_trans (dec_trivial) Hn,
show int.of_nat n - 3 = int.of_nat (n - 3), rw int.of_nat_sub h3, refl,  exact Hn, rw [ nat.sub_add_cancel], 
show 1 ≤ n - 3, rw nat.le_sub_left_iff_add_le, ring, exact Hn, exact le_trans (dec_trivial) Hn,  exact Hn, 
exfalso, have X : n - 3 ≤ n - 1, rw le_of_sub_le_sub_left_iff n 3 1, exact dec_trivial, exact ge_trans Hn (dec_trivial), exact ge_trans Hn (dec_trivial),
have H5 : some (n - 4 + int.nat_abs (4 + (-1 - ↑(int.nat_abs 2)))) ≤ some (1 + int.nat_abs (2 + (-↑(int.nat_abs 4) - ↑(n - 4)))),
show (n - 4 + 4 - 3 - 1 + 1) ≤ (1 + int.nat_abs (2 + (-↑4 - ↑(n - 4)))), rw nat.sub_add_cancel, rw nat.sub_add_cancel,
--------------------------------------------------------------
let m := n - 4,
  have H1 : m + 4 = n,
    by simp [m, nat.add_sub_cancel' Hn],
  have H2 : 4 - 3 = 1,
    from dec_trivial,
  have H3 : 4 - 4 = 0,
    from dec_trivial,
  rw [← H1, nat.add_sub_assoc, nat.add_sub_assoc, H2, H3, ← add_sub_assoc],
  rw [← int.nat_abs_neg], simp [bit0, -add_comm],
  rw [int.coe_nat_add_one_out, add_comm (1 : ℤ), int.coe_nat_add_one_out],
  rw [int.nat_abs_of_nat, add_comm 1],
  constructor, constructor, constructor,
  from dec_trivial, from dec_trivial,
----------------------------------------------------------------------------
exact Hn,  rw nat.sub_add_cancel, show 1 ≤ n - 3, rw nat.le_sub_right_iff_add_le, show 4 ≤ n, exact Hn, 
exact le_trans (dec_trivial) Hn, exact Hn, exact false.elim (h_5 H5),
 exfalso, have I : some (1 + int.nat_abs (2 + (-↑(int.nat_abs 4) - ↑(n - 4)))) ≤ none, simp, exact false.elim (h_4 I),
 exfalso, rw a at h_3, have P : 3 ∉ (0 : multiset nat), exact not_mem_zero 3, have nh_3 : erase_dup (3 :: 0) = 3 :: 0,
 rw erase_dup_cons_of_not_mem P, rw erase_dup_zero, exact false.elim (h_3 nh_3),
end

--lemma cases_card_1 (x : multiset nat) (n : nat)  (h :∀ a ∈ x, a ≥ 4 ∧ 2 ∣ a) : x = n :: 0 → n = 4 ∨ 



lemma two_point_two_1 (G : sle) (a : nat) : (card (G.chains) ≥ 2) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G:=
begin
intros y H t, 
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl, exfalso, rw h.left at y, simp at y,  exact false.elim (Q y),
exfalso, rw h.left at y, simp at y, exact false.elim (Q y),
exfalso, rw h.left at y, simp at y, exact false.elim (Q y), 
exfalso, rw h.left at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.chains = 0, exact (zero_size G h_2).left, rw e at t, finish,
refl,
exfalso, exact false.elim (h_1 H.right), 
refl, 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
refl,
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
refl, 
exact t, 
end


lemma two_point_two_2 (G : sle) (a : nat) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G:=
begin
intros y z H Ha, dunfold size at y,
 rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
have B : size G = 0, dunfold size, rw h_2, rw h.left, simp, 
exfalso, exact false.elim (h_1 B),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Ha , finish,
exfalso, rw h_3 at Ha, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
have P : filter (λ (x : ℕ), x ≥ 4) (G.chains) = G.chains, exact (H.left).symm, 
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0, rw ← h_5 at d, rw mem_erase_dup at d, 
rw filter_eq_self at P, have H5 := P 3 d, revert H5, exact dec_trivial,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso,have P : filter (λ (x : ℕ), x ≥ 4) (G.chains) = G.chains, exact (H.left).symm, 
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0, rw ← h_3 at d, rw mem_erase_dup at d, 
rw filter_eq_self at P, have H5 := P 3 d, revert H5, exact dec_trivial,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Ha,
end

lemma two_point_two_3 (G : sle) (a : nat) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G:=
begin
intros y z H Ha, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
have B : size G = 0, dunfold size, rw h_2, rw h.left, simp, 
exfalso, exact false.elim (h_1 B),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw H.left at h_1, finish, 
exfalso, rw [H.left, h_3] at y, simp at y, exact false.elim (Q y),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, have p : card G.loops = 1, rw h_2, simp, exact false.elim (z (and.intro H.left p)),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw [H.left, h_5] at y, simp at y, exact false.elim (Q y),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Ha,
end





lemma two_point_two_4_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have m : G.chains = 0, exact (zero_size G h_2).left, rw [m, h_1] at y, finish, 
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).right), 
refl, 
exfalso, rw h_2 at H, have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exfalso, rw h_2 at H, have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exfalso,  exact false.elim (h_1 (zero_size G h_4).right),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, rw ← h_3 at h_6, have R : ∃ t, G.chains = 3 :: t, exact exists_cons_of_mem Hl, cases R with t Ht, 
rw Ht at h_6, simp at h_6, have P : 3 ∈ multiset.cons 3 0, finish, rw ← h_3 at P, rw mem_erase_dup at P, 
rw Ht at P, simp at P, rw erase_dup_cons_of_mem P at h_6, finish, 
exfalso,  exact false.elim (h_1 (zero_size G h_4).right),
exfalso, rw h_5 at H, finish, 
exfalso, 
cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_6 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exact Hl,
end


lemma two_point_two_4_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw h_1 at H, finish,
exfalso, rw h_1 at H, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_5 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Hl,
end

lemma two_point_two_4_3 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw h_2 at Hl, finish,
exfalso, rw h_3 at H, finish,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),  
exfalso, exact false.elim (h_3 h.left),
exfalso, rw h_1 at H, finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_5 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exact Hl,
end

lemma count_imp_card {m : multiset nat} {a b : nat} : b ≤ count a m  → card m ≥ b :=
begin
intro x, rw le_count_iff_repeat_le at x, have h : card (repeat a b) ≤ card m, exact card_le_of_le x,
rw card_repeat at h, finish, 
end



lemma count_ge_2_mem_erase {a : nat} {c : multiset nat} : 2 ≤ count a c → a ∈ erase c a :=
begin
intro x,
rw ← count_pos , rw count_erase_self, rw le_iff_eq_or_lt at x, cases x,
rw ← x, exact dec_trivial, have h : succ 0 < count a c, exact lt_trans dec_trivial x, 
exact lt_pred_of_succ_lt h,     
end


lemma two_point_two_5 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
→ 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G:=
begin
intros y z H d, dunfold size at y,
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.chains = 0, exact (zero_size G h_2).left, rw e at d, finish,
refl,
exfalso, have e : G.chains = 0, exact (zero_size G h_3).left, rw e at d, finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim (Q H),
exfalso, exact false.elim (h_5 H.right),
exfalso, exact false.elim (h_1 (zero_size G h_4).right), 
exfalso, rw h_5 at d, finish,
refl,
exfalso, exact false.elim (h_6 H.right),
exfalso, exact false.elim (h_1 (zero_size G h_4).right), 
exfalso, rw h_5 at d, finish,
exfalso, rw ← cons_erase d at h_6,
have P : 3 ∈ erase G.chains 3, exact count_ge_2_mem_erase H.left, 
rw erase_dup_cons_of_mem P at h_6, exact false.elim (h_3 h_6), -- rw ← cons_erase d at h_6, 
refl,
exact d,
end

lemma two_point_two_6_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
→ 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw h_2 at Hl, finish,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, exact false.elim ( h_3 H.right),
exfalso, exact false.elim ( h_3 H.right),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
refl,
exact Hl,
end




lemma two_point_two_6_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
→ 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exact Hl,
end


lemma two_point_two_7_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2)
→ 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_3).right, rw e at Hl , finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim ( Q H.right),
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
refl,
refl,
exact Hl,
end




lemma two_point_two_7_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2)
→ 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw h_1 at H, finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_3).right, rw e at Hl , finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim ( Q H.right),
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
refl,
refl,
exact Hl,
end

lemma sum_rem_c (a : multiset nat) (c : nat): c ∈ a → sum (erase a c) = sum a - c :=
begin 
intro Hc, have h : ∃ t, a = c :: t, exact exists_cons_of_mem Hc, cases h with t Ht, rw Ht,
 simp, rw add_comm, rw nat.add_sub_cancel,
end

lemma card_rem_c (a : multiset nat) (c : nat): c ∈ a → card (erase a c) = card a - 1 :=
begin 
intro Hc, have h : ∃ t, a = c :: t, exact exists_cons_of_mem Hc, cases h with t Ht, rw Ht,
 simp, rw add_comm, rw nat.add_sub_cancel,
end


lemma multiset_sum_ge_c (a : multiset nat) (c : nat) : c ∈ a → sum a ≥ c := 
begin
intro x, have h : ∃ t, a = c :: t, exact exists_cons_of_mem x, cases h with t Ht, rw Ht,
 simp, induction  (sum t) with n Hn, finish, rw succ_eq_add_one, rw ← add_assoc,  
 show c ≤ c + n + 1, rw le_add_one_iff , left, exact Hn, 
end


lemma multiset_card_ge_1 (a : multiset nat) (c : nat) : c ∈ a → card a ≥ 1 := 
begin
intro x, have h : ∃ t, a = c :: t, exact exists_cons_of_mem x, cases h with t Ht, rw Ht,
 simp, induction  (card t) with n Hn, finish, rw succ_eq_add_one, rw ← add_assoc,  
 show 1 ≤ 1 + n + 1, rw le_add_one_iff , left, exact Hn, 
end


lemma rem_three_chain_cv (G : sle) : 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G → cv (rem_chain_from_sle G 3) = cv G + 1 :=
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_chain, unfold fcv, rw sum_rem_c G.chains 3 x, rw card_rem_c G.chains 3 x, 
rw ← add_assoc, 
let n := sum (G.chains) - 3, let m := (card (G.chains) - 1),
have Hn : sum (G.chains) ≥ 3, exact multiset_sum_ge_c G.chains 3 x, 
have Hn1 : sum (G.chains) = n + 3, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.chains) ≥ 1, exact multiset_card_ge_1 G.chains 3 x, 
have Hm1 : card (G.chains) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib,
simp, show int.of_nat n + (int.of_nat (sum (G.loops)) + (↑(tb G) + (-(↑m * 4) + -(↑(card (G.loops)) * 8)))) =
    1 + (int.of_nat (n) + 3 + (int.of_nat (sum (G.loops)) + (↑(tb G) + (-4 + (-(↑m * 4) + -(↑(card (G.loops)) * 8)))))),  
rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, rw add_comm 1 (int.of_nat n), 
show int.of_nat n + int.of_nat (sum (G.loops)) + ↑(tb G) + -(↑m * 4) + -(↑(card (G.loops)) * 8) =
    int.of_nat n + 4 + int.of_nat (sum (G.loops)) + ↑(tb G) + -4 + -(↑m * 4) + -(↑(card (G.loops)) * 8), simp, 
 exact x,
end



lemma rem_three_chain_to_cb_ge_3 (G : sle) : 2 ≤ cv G → 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G → cv (rem_chain_from_sle G 3) ≥ 3:=
begin 
intros H x y , rw [rem_three_chain_cv G x y], show 3 ≤ (cv G) + 1, rw le_iff_eq_or_lt at H, cases H, rw ← H, simp, 
rw le_iff_eq_or_lt, right, rw int.lt_add_one_iff, rw ← int.add_one_le_iff at H, finish,
end


lemma rem_four_loop_cv (G : sle) : 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G → cv (rem_loop_from_sle G 4) = cv G + 4 := 
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_loop, unfold fcv, rw sum_rem_c G.loops 4 x, rw card_rem_c G.loops 4 x, 
rw ← add_assoc, 
let n := sum (G.loops) - 4, let m := (card (G.loops) - 1),
have Hn : sum (G.loops) ≥ 4, exact multiset_sum_ge_c G.loops 4 x, 
have Hn1 : sum (G.loops) = n + 4, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.loops) ≥ 1, exact multiset_card_ge_1 G.loops 4 x, 
have Hm1 : card (G.loops) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib, simp, 
show int.of_nat n + (int.of_nat (sum (G.chains)) + (↑(tb G) + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))) =
    4 + (int.of_nat (sum (G.chains)) + (↑(tb G) + (int.of_nat n + 4 + (-8 + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))))),
 rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, simp, 
  rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
show int.of_nat (sum (G.chains)) + ↑(tb G) + -(↑m * 8) + -(↑(card (G.chains)) * 4) =
    8 + int.of_nat (sum (G.chains)) + ↑(tb G) + -8 + -(↑m * 8) + -(↑(card (G.chains)) * 4),
    simp, exact x,
end


lemma rem_four_loop_to_cb_ge_4 (G : sle) : 2 ≤ cv G → 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G → cv (rem_loop_from_sle G 4) ≥ 4:=
begin 
intros H x y , rw [rem_four_loop_cv G x y], show 4 ≤ (cv G) + 4, rw le_iff_eq_or_lt at H, cases H, rw ← H, simp, 
rw le_iff_eq_or_lt, right,rw lt_add_iff_pos_left, exact lt_trans (dec_trivial) H, 
end


lemma rw_fcv (G : sle) : ∃  (n : ℤ) (H : 0 ≤ n ),  cv G =  n + ↑ (tb G) - count 3 G.chains - 4 * count 4 G.loops - 2 * count 6 G.loops :=
begin 
fapply exists.intro, exact cv G + 2 * count 6 G.loops + 4 * count 4 G.loops + count 3 G.chains - ↑ (tb G), 
fapply exists.intro, unfold cv, 
rw looplemma G.loops (loop468 G.loops G.loops_are_long_and_even), rw count_add, rw count_add, 
rw count_add, rw count_add, simp, 
 sorry, 
simp,  

end


lemma rem_six_loop_cv (G : sle) : 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G → cv (rem_loop_from_sle G 6) = cv G + 2 := 
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_loop, unfold fcv, rw sum_rem_c G.loops 6 x, rw card_rem_c G.loops 6 x, 
rw ← add_assoc, 
let n := sum (G.loops) - 6, let m := (card (G.loops) - 1),
have Hn : sum (G.loops) ≥ 6, exact multiset_sum_ge_c G.loops 6 x, 
have Hn1 : sum (G.loops) = n + 6, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.loops) ≥ 1, exact multiset_card_ge_1 G.loops 6 x, 
have Hm1 : card (G.loops) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib, simp, 
show int.of_nat n + (int.of_nat (sum (G.chains)) + (↑(tb G) + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))) =
    2 + (int.of_nat (sum (G.chains)) + (↑(tb G) + (int.of_nat n + 6 + (-8 + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))))),
 rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, simp, 
  rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
show int.of_nat (sum (G.chains)) + ↑(tb G) + -(↑m * 8) + -(↑(card (G.chains)) * 4) =
    8 + int.of_nat (sum (G.chains)) + ↑(tb G) + -8 + -(↑m * 8) + -(↑(card (G.chains)) * 4),
    simp, exact x,
end



lemma rem_six_loop_to_cb_ge_4 (G : sle) : 2 ≤ cv G → 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G → cv (rem_loop_from_sle G 6) ≥ 4:=
begin 
intros H x y , rw [rem_six_loop_cv G x y], show 4 ≤ (cv G) + 2, rw le_iff_eq_or_lt at H, cases H, rw ← H, exact dec_trivial, 
rw le_iff_eq_or_lt, right, 
show 2 + 2 < cv G + 2, apply add_lt_add_right, exact H, 
end

lemma int_sub_le (a b : ℤ ) : b ≥ 0 →  a - b ≤ a :=
begin
intro x, induction b with t n, finish, exfalso, 
have h : ¬  -[1+ n] ≥ 0, exact dec_trivial,   
exact false.elim (h x),
end

lemma int_le_add (a b : ℤ ) : b ≥ 0 →  a ≤ b + a :=
begin
intro x, induction b with t n, finish, exfalso, 
have h : ¬  -[1+ n] ≥ 0, exact dec_trivial,   
exact false.elim (h x),
end

lemma rem_chain_no_loops_fcv_pos (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → fcv (rem_chain_from_sle G a) ≥ 0 :=
begin 
intros x y, rw fcv_rem_chain G a y, rw x.right, simp, rw card_rem_c G.chains a y, rw sum_rem_c G.chains a y, 
rw x.left, 
show (0: ℤ)  +
      (↑  (sum (filter (λ (x : ℕ), x ≥ 4) (G.chains)) - a) +
         -(↑(card (filter (λ (x : ℕ), x ≥ 4) (G.chains)) - 1) * 4)) ≥
    0,  rw zero_add, sorry
end

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
intros x y, rw fcv_rem_loop G a y, simp, sorry
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
 
theorem two_point_two_ak_chain (G : sle) (a : nat) (h : a ∈ G.chains) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) →  (tb (rem_chain_from_sle G a) = tb G) ∧ (cv (rem_chain_from_sle G a) ≥ 2) → chain_move_is_optimal G a :=
begin
intros x y z, 
have H : (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))), exact two_point_two_ad G x y z,
cases H, cases H with c Hc, cases Hc with t Ht, sorry, sorry,
end

theorem two_point_two_ak_loop (G : sle) (a : nat) (h : a ∈ G.loops) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) →  (tb (rem_loop_from_sle G a) = tb G) ∧ (cv (rem_loop_from_sle G a) ≥ 4) → loop_move_is_optimal G a := 
begin
intros x y z, 
have H : (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))), exact two_point_two_ad G x y z,
cases H, cases H with c Hc, cases Hc with t Ht, sorry, sorry,
end

theorem two_point_two_bk (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) → (int.of_nat (value G) = cv G):=
begin
intros x y z, 
have H : (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))), exact two_point_two_ad G x y z,
cases H, cases H with c Hc, cases Hc with t Ht,
have p : chain_move_is_optimal G c, exact two_point_two_ak_chain G c t x y z Ht,
unfold chain_move_is_optimal at p, rw p,    sorry, sorry,
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
exact two_point_two_bk G x h.left h.right, 
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


theorem three_point_two_1 (G: sle) : ((size G) > 0) → (cv G ≤ 1) → (value G ≤ 4) := sorry



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
cases H, exfalso, unfold cv at y, unfold fcv at y, rw H.right at y, rw H.left at y, simp at y, sorry,
cases H, exfalso,  sorry,
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
rw Ht at h, rw mem_cons at h, cases h, rw h,  sorry, have v : ∃ a, t = 6 :: a,   exact exists_cons_of_mem h, cases v with s Hs, rw Hs at Ht, sorry,
sorry, sorry,
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

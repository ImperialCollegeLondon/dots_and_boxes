import Dotsandboxes__Part1
import Dotsandboxes_Part2

open multiset 

lemma chain34 (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
∀ c ∈ C, c = 3 ∨ c ≥ 4 :=
begin
  intros c Hc,
  have H := HC c Hc,clear HC,clear Hc,
  cases eq_or_lt_of_le H with H1 H1,
    left,exact H1.symm,
    right,exact H1,
end

theorem filter_add_filter_not (α : Type*) (M : multiset α) (p : α → Prop) [decidable_pred p]:
filter p M + filter (λ a, ¬ p a) M = M := 
begin
  rw filter_add_filter,
  have Hleft : filter (λ (a : α), p a ∨ ¬p a) M = M,
    rw filter_eq_self,
    intros;exact decidable.em _,
  have Hright : filter (λ (a : α), p a ∧ ¬p a) M = 0,
    rw filter_eq_nil,
    intros;rw and_not_self;exact id,
  rw [Hleft,Hright],exact add_zero _,
end

theorem loop468' (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
filter (λ l, l = 4) L + filter (λ l, l = 6) L + filter (λ l, l ≥ 8) L = L :=
begin
  have H : filter (λ l, l = 4) L + filter (λ l, l ≠ 4) L = L := by rw filter_add_filter_not,
  let L' := filter (λ l, l ≠ 4) L,
  have H2 : filter (λ l, l = 6) L' + filter (λ l, l ≠ 6) L' = filter (λ l, l ≠ 4) L :=
  by rw filter_add_filter_not,
  rw ←H2 at H,
  rw filter_filter at H,
  rw filter_filter at H,
  conv begin
    to_rhs,
    rw ←H,
  end,
  rw add_assoc,
  congr' 2,
    congr,
    funext,
    apply propext,
    symmetry,
    rw and_iff_left_of_imp,
    intro h,rw h,exact dec_trivial,
  apply filter_congr,
  intros l Hl,
  cases loop468 L HL l Hl,
    simp [h],exact dec_trivial,
  cases h,
    simp [h],exact dec_trivial,
  simp [h],split;intro h2;rw h2 at h;revert h;exact dec_trivial
end

lemma rem_chain_no_loops_fcv_pos' (G : sle) (a : nat) :
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
→ a ∈ G.chains → fcv (rem_chain_from_sle G a) ≥ 0 :=
begin
  intros x y, rw fcv_rem_chain G a y, rw x.right, simp, rw card_rem_c G.chains a y, 
  rw sum_rem_c G.chains a y,
  have H := x.1,
  clear x,
  have H2 := filter_eq_self.1 H.symm,
  show (0 : ℤ) + _ ≥ 0,
  rw zero_add,
  have H3 := exists_cons_of_mem y,
  cases H3 with t Ht,
  rw Ht,
  rw sum_cons,
  rw card_cons,
  rw nat.add_sub_cancel,
  rw nat.add_sub_cancel_left,
  rw ←sub_eq_add_neg,
  show (0 : ℤ) ≤ _,
  rw sub_nonneg,
  suffices : (↑((card t) * 4) : ℤ) ≤ ↑(sum t),
    simpa using this,
  rw int.coe_nat_le_coe_nat_iff,
  have H3 : ∀ (a : ℕ), a ∈ t → a ≥ 4,
    intros a' Ha',
    apply H2,
    rw Ht,
    simp [Ha'],
  revert H3,
  apply multiset.induction_on t,
    simp,
  intros a' t Ht H3,
  rw [card_cons,sum_cons,add_mul,one_mul,add_comm a'],
  have H4 : card t * 4 ≤ sum t,
    apply Ht,
    intros b Hb,
    apply H3,
    simp [Hb],
  apply add_le_add H4,
  apply H3,simp,
end

lemma rw_cv (G : sle) : ∃  (n : ℤ) (H : 0 ≤ n ),  cv G =  n + ↑ (tb G) - count 3 G.chains - 4 * count 4 G.loops - 2 * count 6 G.loops :=
begin
fapply exists.intro, exact cv G + 2 * count 6 G.loops + 4 * count 4 G.loops + count 3 G.chains - ↑ (tb G),
fapply exists.intro, unfold cv,
rw looplemma G.loops (loop468 G.loops G.loops_are_long_and_even), rw count_add, rw count_add,
rw count_add, rw count_add, simp,
 sorry,
simp,

end

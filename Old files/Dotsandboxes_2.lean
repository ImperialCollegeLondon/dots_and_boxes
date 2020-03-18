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

lemma countp_count {α : Type*} [decidable_eq α] {a : α} {s : multiset α} :
countp (λ (b : α), b = a) s = count a s :=
begin
  unfold count,
  congr, -- goal now (λ (b : α), b = a) = eq a
  funext, -- goal now b = a = (a = b)
  apply propext,split;intro h;exact h.symm
end

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

lemma c34 (c : ℕ) (Hc : c ≥ 3) : c = 3 ∨ c ≥ 4 :=
begin
  cases eq_or_lt_of_le Hc with H H,
  left,exact H.symm,
  right,exact H
end

lemma l468 (l : ℕ) (Hl : l ≥ 4 ∧ 2 ∣ l) : l = 4 ∨ l = 6 ∨ l ≥ 8 :=
begin
  cases Hl with Hl He,
  cases eq_or_lt_of_le Hl with H4 H4,
    left,exact H4.symm,
  change 5 ≤ l at H4,
  cases eq_or_lt_of_le H4 with H5 H5,
    exfalso, revert He,rw ←H5,exact dec_trivial,
  clear H4,change 6 ≤ l at H5,
  cases eq_or_lt_of_le H5 with H6 H6,
    right,left,exact H6.symm,
  clear H5,change 7 ≤ l at H6,
  cases eq_or_lt_of_le H6 with H7 H7,
    exfalso,revert He,rw ←H7,exact dec_trivial,
  right,right,exact H7
end


-- loop468 is already in Part1

theorem chain34' (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
filter (λ c, c = 3) C + filter (λ c, c ≥ 4) C = C :=
begin
  have H : filter (λ c, c = 3) C + filter (λ c, c ≠ 3) C = C := by rw filter_add_filter_not,
  suffices : filter (λ (c : ℕ), c ≥ 4) C = filter (λ (c : ℕ), c ≠ 3) C, 
    rwa this,
  apply multiset.filter_congr,
  intros x Hx,
  cases (chain34 C HC x Hx),
    simp [h],exact dec_trivial,
    simp [h],intro h2,rw h2 at h,revert h,exact dec_trivial
end

lemma chain_sum_ge (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
sum C + card (filter (λ c, c = 3) C) ≥ 4 * card C :=
begin
  conv in (sum C) begin
    rw ←chain34' C HC,
  end,
  rw sum_add,
  revert HC,
  apply multiset.induction_on C,
    simp,exact le_refl 0,
  intros n s H1 H2,
  cases c34 n (H2 n $ mem_cons_self _ _) with H3 H4,
    have H4 : ¬ (4 ≤ n),
      rw H3,exact dec_trivial,
    rw @filter_cons_of_neg _ (λ c, c ≥ 4) _ _ s H4,
    rw @filter_cons_of_pos _ (λ c, c = 3) _ _ s H3,
    rw [sum_cons,card_cons,card_cons,mul_add,mul_one],
    rw H3,
    have H5 : (∀ (x : ℕ), x ∈ s → x ≥ 3),
      intros x Hx,apply H2,simp [Hx],
    rw ←add_assoc,
    apply nat.succ_le_succ,
    rw add_comm,
    rw [add_assoc,add_assoc],
    refine nat.add_le_add_left _ 3,
    rw ←add_assoc,
    exact H1 H5,
  have H3 : ¬ (n = 3),
    intro h3,rw h3 at H4,revert H4,exact dec_trivial,
    rw @filter_cons_of_pos _ (λ c, c ≥ 4) _ _ s H4,
    rw @filter_cons_of_neg _ (λ c, c = 3) _ _ s H3,
    rw [sum_cons,card_cons,mul_add,mul_one],
    have H5 : (∀ (x : ℕ), x ∈ s → x ≥ 3),
      intros x Hx,apply H2,simp [Hx],
    have H6 := H1 H5,
    simp,simp at H6,apply add_le_add,exact H4,exact H6
end

lemma loop_sum_ge (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
sum L + 4 * card (filter (λ l, l = 4) L) + 2 * card (filter (λ l, l = 6) L) ≥ 8 * card L :=
begin
  conv in (sum L) begin
    rw ←loop468' L HL,
  end,
  rw sum_add,
  rw sum_add,
  revert HL,
  apply multiset.induction_on L,
    simp,exact le_refl 0,
  intros n s H1 H2,
  cases l468 n (H2 n $ mem_cons_self _ _) with H4 H68,
  { have H6 : ¬ (n = 6),
      rw H4,exact dec_trivial,
    have H8 : ¬ (n ≥ 8),
      rw H4,exact dec_trivial,
    rw @filter_cons_of_neg _ (λ l, l = 6) _ _ s H6,
    rw @filter_cons_of_neg _ (λ l, l ≥ 8) _ _ s H8,
    rw @filter_cons_of_pos _ (λ l, l = 4) _ _ s H4,
    rw [sum_cons,card_cons,card_cons,mul_add,mul_one,mul_add,mul_one],
    rw H4,
    have H5 : (∀ (x : ℕ), x ∈ s → x ≥ 4 ∧ 2 ∣ x),
      intros x Hx,apply H2,simp [Hx],
    have H := H1 H5,
    suffices : 4 + sum (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l = 6) s) +
          sum (filter (λ (l : ℕ), l ≥ 8) s) +
        (4 * card (filter (λ (l : ℕ), l = 4) s) + 4) +
      2 * card (filter (λ (l : ℕ), l = 6) s) = sum (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l = 6) s) + sum (filter (λ (l : ℕ), l ≥ 8) s) +
        4 * card (filter (λ (l : ℕ), l = 4) s) +
      2 * card (filter (λ (l : ℕ), l = 6) s) + 8,
      rw this,exact add_le_add_right H 8,
    suffices : 4 +
      (4 +
         (sum (filter (λ (l : ℕ), l = 4) s) +
            (sum (filter (λ (l : ℕ), l = 6) s) +
               (2 * card (filter (λ (l : ℕ), l = 6) s) +
                  (4 * card (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l ≥ 8) s)))))) =
    8 +
      (sum (filter (λ (l : ℕ), l = 4) s) +
         (sum (filter (λ (l : ℕ), l = 6) s) +
            (2 * card (filter (λ (l : ℕ), l = 6) s) +
               (4 * card (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l ≥ 8) s))))),
    simpa,
    rw ←add_assoc
  },
  cases H68 with H6 H8,
  { have H4 : ¬ (n = 4),
      rw H6,exact dec_trivial,
    have H8 : ¬ (n ≥ 8),
      rw H6,exact dec_trivial,
    rw @filter_cons_of_neg _ (λ l, l = 4) _ _ s H4,
    rw @filter_cons_of_neg _ (λ l, l ≥ 8) _ _ s H8,
    rw @filter_cons_of_pos _ (λ l, l = 6) _ _ s H6,
    rw [sum_cons,card_cons,card_cons,mul_add,mul_one,mul_add,mul_one],
    rw H6,
    have H5 : (∀ (x : ℕ), x ∈ s → x ≥ 4 ∧ 2 ∣ x),
      intros x Hx,apply H2,simp [Hx],
    have H := H1 H5,
    suffices : sum (filter (λ (l : ℕ), l = 4) s) + (6 + sum (filter (λ (l : ℕ), l = 6) s)) +
          sum (filter (λ (l : ℕ), l ≥ 8) s) +
        4 * card (filter (λ (l : ℕ), l = 4) s) +
      (2 * card (filter (λ (l : ℕ), l = 6) s) + 2) =
    sum (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l = 6) s) + sum (filter (λ (l : ℕ), l ≥ 8) s) +
        4 * card (filter (λ (l : ℕ), l = 4) s) +
      2 * card (filter (λ (l : ℕ), l = 6) s) + 8,
      rw this,exact add_le_add_right H 8,
    suffices : 2 +
      (6 +
         (sum (filter (λ (l : ℕ), l = 4) s) +
            (sum (filter (λ (l : ℕ), l = 6) s) +
               (2 * card (filter (λ (l : ℕ), l = 6) s) +
                  (4 * card (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l ≥ 8) s)))))) =
    8 +
      (sum (filter (λ (l : ℕ), l = 4) s) +
         (sum (filter (λ (l : ℕ), l = 6) s) +
            (2 * card (filter (λ (l : ℕ), l = 6) s) +
               (4 * card (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l ≥ 8) s))))),
    simpa,
    rw ←add_assoc,
  },
  { have H4 : ¬ (n = 4),
      intro H4,revert H8,rw H4,exact dec_trivial,
    have H6 : ¬ (n = 6),
      intro H4,revert H8,rw H4,exact dec_trivial,
    rw @filter_cons_of_neg _ (λ l, l = 4) _ _ s H4,
    rw @filter_cons_of_neg _ (λ l, l = 6) _ _ s H6,
    rw @filter_cons_of_pos _ (λ l, l ≥ 8) _ _ s H8,
    rw [sum_cons,card_cons,mul_add,mul_one],
    have H5 : (∀ (x : ℕ), x ∈ s → x ≥ 4 ∧ 2 ∣ x),
      intros x Hx,apply H2,simp [Hx],
    have H := H1 H5,
    suffices : sum (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l = 6) s) +
          (n + sum (filter (λ (l : ℕ), l ≥ 8) s)) +
        4 * card (filter (λ (l : ℕ), l = 4) s) +
      2 * card (filter (λ (l : ℕ), l = 6) s) = sum (filter (λ (l : ℕ), l = 4) s) + sum (filter (λ (l : ℕ), l = 6) s) + sum (filter (λ (l : ℕ), l ≥ 8) s) +
        4 * card (filter (λ (l : ℕ), l = 4) s) +
      2 * card (filter (λ (l : ℕ), l = 6) s) + n,
      rw this,exact add_le_add H H8,
    simp,
  }
end



lemma rw_cv (G : sle) : ∃  (n : ℤ) (H : 0 ≤ n ),  cv G =  n + ↑ (tb G) - count 3 G.chains - 4 * count 4 G.loops - 2 * count 6 G.loops :=
begin
  fapply exists.intro, exact cv G + 2 * count 6 G.loops + 4 * count 4 G.loops + count 3 G.chains - ↑ (tb G),
  fapply exists.intro, unfold cv,
  rw looplemma G.loops (loop468 G.loops G.loops_are_long_and_even), rw count_add, rw count_add,
  rw count_add, rw count_add,
    swap,
    rw _root_.sub_add_cancel,
    rw _root_.add_sub_cancel,
    rw _root_.add_sub_cancel,
    rw _root_.add_sub_cancel,
  unfold fcv,
  unfold tb,
  split_ifs,
  dunfold size at h,
  have HC : G.chains = 0,
    rw ←multiset.card_eq_zero,
    have H := nat.le_add_right (card G.chains) (card G.loops),
    rw h at H,
    rwa ←nat.le_zero_iff,
  have HL : G.loops = 0,
    rw ←multiset.card_eq_zero,
    have H := nat.le_add_left (card G.loops) (card G.chains),
    rw h at H,
    rwa ←nat.le_zero_iff,  
  rw HC,
  rw HL,
  simp,
  { rw h_1,
    suffices : (0 : ℤ) ≤ int.of_nat 0 + (int.of_nat (sum (G.chains)) + (↑(count 3 (G.chains)) + -(↑(card (G.chains)) * 4))),
      simpa,
    show (0 : ℤ) ≤ (0 : ℤ) + _,
    rw zero_add,
    rw [←add_assoc,←sub_eq_add_neg,sub_nonneg],
    show (↑(card (G.chains)) : ℤ) * (↑(4 : ℕ) : ℤ) ≤ ↑(sum (G.chains)) + ↑(count 3 (G.chains)),
    rw ←int.coe_nat_add,
    rw ←int.coe_nat_mul,
    rw int.coe_nat_le,
    have H := chain_sum_ge G.chains G.chains_are_long,
    suffices : card (filter (λ (c : ℕ), c = 3) (G.chains)) = count 3 G.chains,
      rw ←this,
      rw mul_comm,
      exact H,
    have H2 := @count_filter _ _ (λ c, c = 3) _ 3 G.chains rfl,
    rw ←H2,
    rw ←countp_eq_card_filter _,
    simp [eq_comm,count],congr,
  },
  { rw h_2,
    have H0 : (count 6 (filter (λ (l : ℕ), l = 4) (G.loops))) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 6 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l = 6) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    suffices : 0 ≤
    int.of_nat 0 +
      (int.of_nat (sum (G.loops)) +
         (2 * ↑(count 6 (G.loops)) + (4 * ↑(count 4 (G.loops)) + -(↑(card (G.loops)) * 8)))),
    simpa,
    show (0 : ℤ) ≤ 0 + (↑(sum (G.loops)) + _),
    rw zero_add,
    clear h h_1 h_2,
    have H := loop_sum_ge G.loops G.loops_are_long_and_even,
    rw ←add_assoc,
    rw ←add_assoc,
    rw [←sub_eq_add_neg,sub_nonneg],
    show (↑(card (G.loops)) : ℤ) * ↑(8 : ℕ) ≤ ↑(sum (G.loops)) + (2 : ℕ) * ↑(count 6 (G.loops)) + (4 : ℕ) * ↑(count 4 (G.loops)),
    rw ←int.coe_nat_mul,
    rw ←int.coe_nat_mul,
    rw ←int.coe_nat_mul,
    rw ←int.coe_nat_add,
    rw ←int.coe_nat_add,
    rw int.coe_nat_le,
    rw ←(countp_eq_card_filter G.loops) at H,
    rw ←(countp_eq_card_filter G.loops) at H,
    rw countp_count at H,
    rw countp_count at H,
    rwa [add_assoc,add_comm (2 * count 6 G.loops),←add_assoc,mul_comm],
  },
  { have H0 : (count 6 (filter (λ (l : ℕ), l = 4) (G.loops))) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 6 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l = 6) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    suffices : 0 ≤
    int.of_nat (sum (G.chains)) +
      (int.of_nat (sum (G.loops)) +
         (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * 4) +
               (-(↑(card (G.loops)) * 8) + (2 * ↑(count 6 (G.loops)) + 4 * ↑(count 4 (G.loops))))))),
    simpa,
    have HL := loop_sum_ge G.loops G.loops_are_long_and_even,
    have HC := chain_sum_ge G.chains G.chains_are_long,
    rw [←countp_eq_card_filter,countp_count] at HL,
    rw [←countp_eq_card_filter,countp_count] at HL,
    rw [←countp_eq_card_filter,countp_count] at HC,
    show (0 : ℤ) ≤ ↑(sum (G.chains)) +
      (↑(sum (G.loops)) + (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * (4 : ℕ)) +
               (-(↑(card (G.loops)) * (8 : ℕ)) + ((2 : ℕ) * ↑(count 6 (G.loops)) + (4 : ℕ) * ↑(count 4 (G.loops))))))),
    have H : 
     8 * card (G.loops) + 4 * card (G.chains)
    ≤
    (sum (G.loops) + 4 * count 4 (G.loops) + 2 * count 6 (G.loops)) + (sum (G.chains) + count 3 (G.chains)) 
     ,
      exact add_le_add HL HC,
    rw [←int.coe_nat_le,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add] at H,
    rw ←sub_nonneg at H,
    suffices : (↑(sum (G.loops)) : ℤ) + ↑(4 * count 4 (G.loops)) + ↑(2 * count 6 (G.loops)) +
        (↑(sum (G.chains)) + ↑(count 3 (G.chains))) -
      (↑(8 * card (G.loops)) + ↑(4 * card (G.chains))) = ↑(sum (G.chains)) +
      (↑(sum (G.loops)) +
         (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * ↑4) +
               (-(↑(card (G.loops)) * ↑8) + (↑2 * ↑(count 6 (G.loops)) + ↑4 * ↑(count 4 (G.loops))))))),
      rwa ←this,
    
    rw [←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_add,mul_comm _ 4,mul_comm _ 8],
    simp,
  },
  { have H0 : (count 6 (filter (λ (l : ℕ), l = 4) (G.loops))) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 6 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l = 6) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    have H0 : count 4 (filter (λ (l : ℕ), l ≥ 8) (G.loops)) = 0,
      apply count_filter_eq_zero,exact dec_trivial,
    rw H0, clear H0,
    suffices : 0 ≤
    int.of_nat (sum (G.chains)) +
      (int.of_nat (sum (G.loops)) +
         (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * 4) +
               (-(↑(card (G.loops)) * 8) + (2 * ↑(count 6 (G.loops)) + 4 * ↑(count 4 (G.loops))))))),
    simpa,
    have HL := loop_sum_ge G.loops G.loops_are_long_and_even,
    have HC := chain_sum_ge G.chains G.chains_are_long,
    rw [←countp_eq_card_filter,countp_count] at HL,
    rw [←countp_eq_card_filter,countp_count] at HL,
    rw [←countp_eq_card_filter,countp_count] at HC,
    show (0 : ℤ) ≤ ↑(sum (G.chains)) +
      (↑(sum (G.loops)) + (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * (4 : ℕ)) +
               (-(↑(card (G.loops)) * (8 : ℕ)) + ((2 : ℕ) * ↑(count 6 (G.loops)) + (4 : ℕ) * ↑(count 4 (G.loops))))))),
    have H : 
     8 * card (G.loops) + 4 * card (G.chains)
    ≤
    (sum (G.loops) + 4 * count 4 (G.loops) + 2 * count 6 (G.loops)) + (sum (G.chains) + count 3 (G.chains)) 
     ,
      exact add_le_add HL HC,
    rw [←int.coe_nat_le,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add,int.coe_nat_add] at H,
    rw ←sub_nonneg at H,
    suffices : (↑(sum (G.loops)) : ℤ) + ↑(4 * count 4 (G.loops)) + ↑(2 * count 6 (G.loops)) +
        (↑(sum (G.chains)) + ↑(count 3 (G.chains))) -
      (↑(8 * card (G.loops)) + ↑(4 * card (G.chains))) = ↑(sum (G.chains)) +
      (↑(sum (G.loops)) +
         (↑(count 3 (G.chains)) +
            (-(↑(card (G.chains)) * ↑4) +
               (-(↑(card (G.loops)) * ↑8) + (↑2 * ↑(count 6 (G.loops)) + ↑4 * ↑(count 4 (G.loops))))))),
      rwa ←this,
    
    rw [←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_add,mul_comm _ 4,mul_comm _ 8],
    simp,
  }
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


lemma rem_chain_no_loops_fcv_pos (G : sle) (a : nat) :
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

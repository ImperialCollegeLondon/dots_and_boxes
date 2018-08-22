import Dotsandboxes__Part1
import Dotsandboxes_2_1

open multiset 

lemma countp_count {α : Type*} [decidable_eq α] {a : α} {s : multiset α} :
countp (λ (b : α), b = a) s = count a s :=
begin
  unfold count,
  congr, -- goal now (λ (b : α), b = a) = eq a
  funext, -- goal now b = a = (a = b)
  apply propext,split;intro h;exact h.symm
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

lemma chain34 (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
∀ c ∈ C, c = 3 ∨ c ≥ 4 :=
begin
  intros c Hc,
  exact c34 c (HC c Hc),
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
  apply multiset.filter_congr, -- this is in the most recent mathlib
  intros l Hl,
  cases loop468 L HL l Hl,
    simp [h],exact dec_trivial,
  cases h,
    simp [h],exact dec_trivial,
  simp [h],split;intro h2;rw h2 at h;revert h;exact dec_trivial
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
  rw count_add, rw count_add,
    swap,
    rw _root_.sub_add_cancel,
    rw _root_.add_sub_cancel,
    rw _root_.add_sub_cancel,
    rw _root_.add_sub_cancel,
  unfold fcv,
  unfold tb,
  split_ifs,
  unfold size at h,
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

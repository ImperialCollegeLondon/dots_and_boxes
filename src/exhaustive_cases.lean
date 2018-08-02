import data.multiset

structure sle :=
(chains : multiset ℕ)
(chains_are_long : ∀ x ∈ chains, x ≥ 3)
(loops : multiset ℕ)
(loops_are_long_and_even : ∀ x ∈ loops, x ≥ 4 ∧ 2 ∣ x)

-- I just PR'd these to mathlib; until they get accepted you'll need them
namespace multiset 

theorem repeat_one {α : Type*} {a : α} : repeat a 1 = a :: 0 :=
(eq_repeat'.2 (λ b,mem_singleton.1 : ∀ b ∈ a :: 0, b = a)).symm

@[simp] theorem erase_dup_singleton {α : Type*} [decidable_eq α] {a : α} : erase_dup (a :: 0) = a :: 0 :=
  erase_dup_cons_of_not_mem $ not_mem_zero a

end multiset

-- proof starts here
open multiset 

lemma loop468 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
∀ l ∈ L, l = 4 ∨ l = 6 ∨ l ≥ 8 :=
begin
  intros l Hl,
  have H := HL l Hl,clear HL,clear Hl,
  cases H with Hl He,
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



lemma cases_for_C (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
  C = 0 
∨ C = 3 :: 0 
∨ (∃ n : ℕ, n ≥ 2 ∧ C = repeat 3 n) 
∨ (3 ∈ C ∧ ∃ c : ℕ, c ≥ 4 ∧ c ∈ C) 
∨ (3 ∉ C ∧ ∃ c : ℕ, c ≥ 4 ∧ c ∈ C)
:= begin
  /- If the next line gives error

  by_cases tactic failed, type of given expression is not decidable

  then your mathlib needs updating because Chris fixed this a couple of weeks ago
  -/
  by_cases H4 : (∃ c ∈ C, c ≥ 4), 
  { by_cases H3 : (3 ∈ C),
      right,right,right,left,split,assumption,
        cases H4 with c Hc,existsi c,cases Hc with Hc1 Hc2,exact ⟨Hc2,Hc1⟩,
      right,right,right,right,split,assumption,
        cases H4 with c Hc,existsi c,cases Hc with Hc1 Hc2,exact ⟨Hc2,Hc1⟩,
  },
  have H3 : ∀ c ∈ C, c = 3,
    intros c Hc,
    cases (eq_or_lt_of_le $ HC c Hc) with H H,
      exact H.symm,
      exfalso,apply H4,existsi c,existsi Hc,exact H,
  have Hrep := eq_repeat'.2 H3,
  cases H : C.card,
    left,rwa ←card_eq_zero,
  cases n with d Hd,
    right,left,
    rw [Hrep,H,repeat_one],
  right,right,left,
  existsi d+2,
  split,exact nat.le_add_left 2 d,
  rw Hrep,rw H
end 

-- C is empty
-- 3 ∉ C ∧ ∃ c, c ≥ 4 ∧ c ∈ C 
lemma cases_for_L1 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
  L = 0
∨ ¬ (L = 0) ∧ 4 ∉ L ∧ 6 ∉ L
∨ 4 ∈ L 
∨ 6 ∈ L 
:= begin
  by_cases H : (L = 0),
    left,assumption,
  by_cases H4 : 4 ∈ L,
    right,right,left,assumption,
  by_cases H6 : 6 ∈ L,
    right,right,right,assumption,
  right,left,split,assumption,split;assumption
end

-- C = {3}
lemma cases_for_L2 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
  (4 ∉ L ∧ 6 ∉ L)
∨ ((4 ∈ L ∨ 6 ∈ L) ∧ card L ≥ 2)
∨ card L = 1
:= begin
  cases H : card L,
    left,rw card_eq_zero at H,rw H,simp,
  cases n with d,
    right,right,refl,
  by_cases H4 : 4 ∈ L,
    right,left,split,left,assumption,exact dec_trivial,
    by_cases H6 : 6 ∈ L,
      right,left,split,right,assumption,exact dec_trivial,
      left,exact ⟨H4,H6⟩
end 

lemma exhaustive_cases (G : sle) :
  (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 )
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2) :=
begin
  have HC := cases_for_C G.chains G.chains_are_long,
  cases HC,
  { -- C empty
    have HL := cases_for_L1 G.loops G.loops_are_long_and_even,
    cases HL,
    { right,left,rw HC,rw HL,split,refl,refl
    },
    cases HL,
    { right,right,left,rw HC,split,refl,
      split,swap,exact HL.1,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.2.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2.2,rwa ←H2,
      exact H2,
    },
    right,right,right,right,right,right,left,split,
      exact HL,
      exact HC
  },
  cases HC,
  { -- C = {3}
    have HL := cases_for_L2 G.loops G.loops_are_long_and_even,
    cases HL,
    { right,right,right,left,
      split,exact HC,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2,rwa ←H2,
      exact H2,
    },
    cases HL,
    { right,right,right,right,right,right,right,
      split,exact HL.1,
      split,exact HC,
      exact HL.2
    },
    { left,
      exact ⟨HC,HL⟩
    }
  },
  cases HC,
  { -- C={3,3,...,3}
    cases HC with n Hn,cases Hn with Hn HC,
    right,right,right,right,right,left,
    split,rw HC,rw [count_repeat],exact Hn,
    rw [HC],rw ←erase_dup_singleton,
    rw erase_dup_ext,intro l,split,
      intro H,rw (eq_of_mem_repeat H),rw mem_singleton,
    intro H,rw mem_singleton at H,rw H,rw [←count_pos,count_repeat],
      exact lt_of_lt_of_le dec_trivial Hn
  },
  cases HC,
  { -- 3 ∈ C ∧ ∃ c >= 4, c ∈ C
    right,right,right,right,left,
    split,left,exact HC.1,
    simp [HC],
  },
  -- 3 ∉ C ∧ ∃ c, c ≥ 4 ∧ c ∈ C 
  have HL := cases_for_L1 G.loops G.loops_are_long_and_even,
  cases HL,
  { right,left,split,swap,exact HL,
    symmetry,rw filter_eq_self,
    intros c Hc,
    have H := G.chains_are_long c Hc,
    cases eq_or_lt_of_le H with H2 H2,
      exfalso,apply HC.left,rwa ←H2 at Hc,
      exact H2,
  },
    cases HL,
    { right,right,left,
      split,symmetry,rw filter_eq_self,
        intros c Hc,    
        have H := G.chains_are_long c Hc,
        cases eq_or_lt_of_le H with H2 H2,
        exfalso,apply HC.left,rwa ←H2 at Hc,
        exact H2,
      split,swap,exact HL.1,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.2.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2.2,rwa ←H2,
      exact H2,
    },
    right,right,right,right,left,split,
      right,exact HL,
      simp [HC.right],
end 

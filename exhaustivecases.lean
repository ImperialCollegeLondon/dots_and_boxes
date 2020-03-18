import sle.basic
import data.multiset

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

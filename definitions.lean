@[derive decidable_eq]
structure simple_loony_endgame :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 4)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, x ≥ 8)
(long_loops_are_even : ∀ x ∈ long_loops, 2 ∣ x)

definition empty_game : simple_loony_endgame :=
{ three_chains := 0,
  four_loops := 0,
  six_loops := 0,
  long_chains := multiset.zero,
  long_chains_are_long := λ x Hx, false.elim Hx,
  long_loops := {},
  long_loops_are_long := λ x Hx, false.elim Hx,
  long_loops_are_even := λ x Hx, false.elim Hx 
}

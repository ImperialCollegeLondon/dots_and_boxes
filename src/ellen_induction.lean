import Dotsandboxes__Part1

/- my proposal for an inductive hypothesis-/
theorem sle.induction_on (p : sle → Sort*)
(H0 : p empty_game_sle)
(Hchain : ∀ (G : sle) (c : ℕ) (Hc : c ≥ 3), p G → p (cons_chain_to_sle G c Hc))
(Hloop : ∀ (G : sle) (l : ℕ) (Hl : l ≥ 4) (Pl : 2 ∣ l), p G → p (cons_loop_to_sle G l Hl Pl)) :
∀ G : sle, p G := sorry 

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


import Dotsandboxes__Part1

open multiset

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
  unfold size,
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
  unfold size,
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

#exit

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
import extended_N_le tactic.ring

-- Given a multiset s of chain lengths (each of which need to be >= 3 for this
-- function to make sense) this returns the value (to the person whose move it is not)
-- of the game.

def chain_value (s0 : multiset ℕ) : ℕ := 
multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs (2 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval (chain_value {4,5,6}) -- 7
#eval chain_value {3,3,3,3,3,3,3,3}

def loop_value (s0 : multiset ℕ) : ℕ := multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval loop_value {4,4,4,4}

@[derive decidable_eq]
structure sle' :=
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 3)
(long_loops : multiset ℕ)
(long_loops_are_long_and_even : ∀ x ∈ long_loops, x ≥ 4 ∧ 2 ∣ x)

definition value_aux (C : multiset ℕ) : multiset ℕ → ℕ := 
  multiset.strong_induction_on C (λ C2 HC L,(
    multiset.strong_induction_on L (λ L2 HL,
      multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C2), a - 2 + int.nat_abs (2 - HC (C2.erase a) (multiset.erase_lt.2 h) L2))
      C2 (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L2), a - 4 +int.nat_abs (4 - HL (L2.erase a) (multiset.erase_lt.2 h)))
      L2 (λ _,id))
    )
  ))

definition G0 : sle' :=
{ long_chains := {3,3,3,3,8},
  long_chains_are_long := dec_trivial,
  long_loops := {4},
  long_loops_are_long_and_even := dec_trivial
}

definition value (G : sle') := value_aux G.long_chains G.long_loops

definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

definition size (G : sle') : ℕ := size_aux G.long_chains G.long_loops

definition fcv_aux (C L : multiset ℕ) : ℤ := ↑(multiset.sum C + multiset.sum L) 
  - 4 * multiset.card C - 8 * multiset.card L

definition fcv (G : sle') : ℤ := fcv_aux G.long_chains G.long_loops

-- Chris and Simon decidability thing
instance decidable_exists_multiset {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) := quotient.rec_on s
list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

instance (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ 4),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

definition tb_aux (C L : multiset ℕ) : ℕ := if (C = 0 ∧ L = 0) then 0 else
  if L = 0 then 4 else
  if C = 0 then 8 else
  if ∃ a : ℕ, a ≥ 4 ∧ a ∈ C then 4 else 
  6

definition tb (G : sle') : ℕ := tb_aux G.long_chains G.long_loops

definition cv_aux (C L : multiset ℕ) : ℤ := fcv_aux C L + tb_aux C L
definition cv (G : sle') : ℤ := fcv G + tb G

open nat 

definition empty_game : sle' := {long_chains := ∅,long_chains_are_long := dec_trivial, 
  long_loops := ∅, long_loops_are_long_and_even := dec_trivial}

lemma cv_zero : cv empty_game = 0 := dec_trivial 

definition single_chain (c : ℕ) (Hc : c ≥ 3) : sle' :=
{ long_chains := {c},
  long_chains_are_long := λ x H, begin
  rwa multiset.mem_singleton.1 H,
  end ,
  long_loops := ∅,
  long_loops_are_long_and_even := dec_trivial
}

@[simp] lemma multiset.sum_singleton {α : Type} [add_comm_monoid α]
(c : α) : multiset.sum (c :: 0) = c := begin rw multiset.sum_cons c 0,exact add_zero c end

@[simp] lemma multiset.sum_singleton' {α : Type} [add_comm_monoid α]
(c : α) : multiset.sum {c} = c := multiset.sum_singleton c 

lemma cv_one_chain (c : ℕ) : cv_aux {c} 0 = c :=
begin
  unfold cv_aux tb_aux,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero c,exact h.left},
  unfold fcv_aux,
  rw [multiset.sum_zero,multiset.card_zero],
  simp,ring 
end 

lemma cv_one_loop (l : ℕ) : cv_aux 0 {l} = l :=
begin
  unfold cv_aux tb_aux,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero l,exact h.2},
  { exfalso, apply multiset.singleton_ne_zero l,exact h_1},
  unfold fcv_aux,
  rw [multiset.sum_zero,multiset.card_zero],
  simp,ring
end

open multiset 
#check @strong_induction_on 
#print prefix multiset.strong_induction_on 

theorem strong_induction_eq {α : Type} {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]

@[simp] lemma v_empty : value_aux 0 0 = 0 :=
begin
  unfold value_aux, -- strong_induction hell
  rw strong_induction_eq, -- goal now one page long
  rw strong_induction_eq, -- goal now two pages long
  simp,
end 

-- I don't have the tools for this yet
lemma v_one_chain (c : ℕ) (h : c ≥ 3) : value_aux (c :: 0) 0 = c :=
begin
  unfold value_aux,
  rw strong_induction_eq,
  rw strong_induction_eq,
  simp,
  rw strong_induction_eq,
  rw strong_induction_eq,
  simp,
  show 2 + (c - 2) = c,
  rw add_comm,refine nat.sub_add_cancel _,
  exact le_trans (show 2 ≤ 3, by exact dec_trivial) h,
end

-- we are getting somewhere!

lemma sum_one {a b : ℕ} : a + b = 1 → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) :=
begin
  intro H,
  cases b,
  { rw add_zero at H,rw H,right,simp},
  cases b,
  { left,split,change _ = 0 + 1 at H,exact add_right_cancel H,refl},
  change succ (succ (a + b)) = succ 0 at H,
  exfalso,exact nat.no_confusion (nat.succ_inj H),
end 

lemma one_comp_case (G : sle') : ((size G) = 1) → (cv G = value G) := 
begin
  intro H,
  have H₂ := sum_one H,
  cases H₂,
  { have H₃ : G.long_chains = ∅ := multiset.card_eq_zero.1 H₂.left,
    have H₄ : G.long_loops ≠ ∅,
      intro H,rw multiset.card_eq_zero.2 H₃ at H₂,rw H at H₂,have H₄ : 0 = 1 := H₂.right,
      revert H₄,simp,
    unfold cv tb tb_aux,
    split_ifs,
    { exact false.elim (H₄ h.right)},
    { unfold fcv,
      sorry
    },
  },
  sorry
end 

#exit 


lemma loop_and_three_chain_case (G : simple_loony_endgame) : (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) → (cv_G G = value G) :=
sorry

lemma three_point_one (G : simple_loony_endgame) : ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  (value G ≥ 2) := sorry



/-
definition multiset.sum {α : Type} [has_add α] [has_zero α] (s : multiset α) : α := multiset.fold (+) 0 s 
def fcv_G (G : sle') := 
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G) 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_chains G)) + 1)*4 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_loops G)) + 2)*8 

lemma one_comp_case (G : sle') : (size G) = 1) → (cv_G G = v_G G) := sorry


#eval value G -- gives 0, which looks right

-/

/- Ellen Challenges!

lemma one_comp_case (G : simple_loony_endgame) : ((size_G G) = 1) → (cv_G G = v_G G) := sorry

lemma loop_and_three_chain_case (G : simple_loony_endgame) : (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) → (cv_G G = value G) :=
sorry

lemma three_point_one (G : simple_loony_endgame) : ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  (value G ≥ 2) := sorry


-/
import extended_N_le

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

definition G : sle' :=
{ long_chains := {3,3,3,3,8},
  long_chains_are_long := dec_trivial,
  long_loops := {4},
  long_loops_are_long_and_even := dec_trivial
}

definition value (G : sle') := value_aux G.long_chains G.long_loops

definition size (G : sle') : ℕ := multiset.card G.long_chains + multiset.card G.long_loops 

#exit 
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

#eval multiset.fold (nat.add) 0 {3,3,4,5}
-/

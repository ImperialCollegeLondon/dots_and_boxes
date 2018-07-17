import extended_N_le tactic.ring

-- simplified version of SLE (because I want easy access to the multisets of loops and chains)
@[derive decidable_eq]
structure sle :=
(chains : multiset ℕ)
(chains_are_long : ∀ x ∈ chains, x ≥ 3)
(loops : multiset ℕ)
(loops_are_long_and_even : ∀ x ∈ loops, x ≥ 4 ∧ 2 ∣ x)


definition empty_game : sle := {chains := ∅,chains_are_long := dec_trivial, 
  loops := ∅, loops_are_long_and_even := dec_trivial}

definition example_game : sle :=
{ chains := {3,3,3,3,8},
  chains_are_long := dec_trivial,
  loops := {4},
  loops_are_long_and_even := dec_trivial
}

-- note: the 20 lines below are just WARM-UP -- it's KB practising for the real definitions.

-- Given a multiset s of chain lengths (each of which need to be >= 3 for this
-- function to make sense) this returns the value (to the person whose move it is not)
-- of the game.

/-
def chain_value (s0 : multiset ℕ) : ℕ := 
multiset.strong_induction_on s0 $ 
  λ s H,multiset.N_min $ multiset.pmap
    (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs (2 - H (s.erase a) (multiset.erase_lt.2 h))) 
    s 
    (λ a, id)

--#eval (chain_value {4,5,6}) -- 7
--#eval chain_value {3,3,3,3,3,3,3,3} -- 2

def loop_value (s0 : multiset ℕ) : ℕ := multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

--#eval loop_value {4,4,4,4}
-/
-- Here is some technical induction thing:

open multiset 

/-

-- equation lemma for multiset 

theorem multiset.strong_induction_eq {α : Type} {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]

-- this is the real definition of value, using strong induction on multisets.

definition value_aux_orig (C : multiset ℕ) : multiset ℕ → ℕ := 
  multiset.strong_induction_on C (λ C2 HC L,(
    multiset.strong_induction_on L (λ L2 HL,
      multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C2), a - 2 + int.nat_abs (2 - HC (C2.erase a) (multiset.erase_lt.2 h) L2))
      C2 (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L2), a - 4 +int.nat_abs (4 - HL (L2.erase a) (multiset.erase_lt.2 h)))
      L2 (λ _,id))
    )
  ))

-- I couldn't prove the equation lemma with this defintion.
-/

-- This should be the same definition, built using the equation compiler.

def value_aux : multiset ℕ → multiset ℕ → ℕ
| C L := multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C), 
        have multiset.card (C.erase a) < multiset.card C,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card (C.erase a) + multiset.card L < multiset.card C + multiset.card L, 
--          from add_lt_add_right (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
        a - 2 + int.nat_abs (2 - value_aux (C.erase a) L))
        C (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L), 
        have multiset.card (L.erase a) < multiset.card L,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card C + multiset.card (multiset.erase L a) < multiset.card C + multiset.card L, 
--          from add_lt_add_left (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
        a - 4 +int.nat_abs (4 - value_aux C (L.erase a)))
        L (λ _,id))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf 
  (λ CL, multiset.card CL.fst + multiset.card CL.snd)⟩]}

/- These definitions have been shoehorned into Lean, and for both of them 
   we now need to prove the key property, namely
-/

/-
lemma value_aux_orig_eq (C L : multiset ℕ) : 
value_aux C L = multiset.N_min 
  (multiset.pmap
    (λ a (h : a ∈ C), 
      a - 2 + int.nat_abs (2 - value_aux_orig (C.erase a) L))
        C (λ _,id) 
  + multiset.pmap 
    (λ a (h : a ∈ L), 
      a - 4 +int.nat_abs (4 - value_aux_orig C (L.erase a)))
        L (λ _,id)
  ) :=
begin
  show ((multiset.strong_induction_on C (λ C2 HC L,(
    multiset.strong_induction_on L (λ L2 HL,
      multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C2), a - 2 + int.nat_abs (2 - HC (C2.erase a) (multiset.erase_lt.2 h) L2))
      C2 (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L2), a - 4 +int.nat_abs (4 - HL (L2.erase a) (multiset.erase_lt.2 h)))
      L2 (λ _,id))
    )
  ))) : multiset ℕ → ℕ) L = _,
  rw multiset.strong_induction_eq C,
  dsimp,
  rw multiset.strong_induction_eq L,
  dsimp,
  congr,funext,congr,
  sorry
end 
-/

lemma value_aux_eq (C L : multiset ℕ) : 
value_aux C L = multiset.N_min 
  (multiset.pmap
    (λ a (h : a ∈ C), 
      a - 2 + int.nat_abs (2 - value_aux (C.erase a) L))
        C (λ _,id) 
  + multiset.pmap 
    (λ a (h : a ∈ L), 
      a - 4 +int.nat_abs (4 - value_aux C (L.erase a)))
        L (λ _,id)
  ) := value_aux._main.equations._eqn_1 C L 

definition value (G : sle) := value_aux G.chains G.loops

definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

definition size (G : sle) : ℕ := size_aux G.chains G.loops

definition fcv_aux (C L : multiset ℕ) : ℤ := ↑(multiset.sum C + multiset.sum L) 
  - 4 * multiset.card C - 8 * multiset.card L

definition fcv (G : sle) : ℤ := fcv_aux G.chains G.loops

-- Chris and Simon decidability thing
instance decidable_exists_multiset {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) := quotient.rec_on s
list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

instance (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ 4),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

-- without those 6 lines of gobble-de-gook above, the below lines don't work
definition tb_aux (C L : multiset ℕ) : ℕ := if (C = 0 ∧ L = 0) then 0 else
  if L = 0 then 4 else
  if C = 0 then 8 else
  if ∃ a : ℕ, a ≥ 4 ∧ a ∈ C then 4 else 
  6

definition tb (G : sle) : ℕ := tb_aux G.chains G.loops

definition cv_aux (C L : multiset ℕ) : ℤ := fcv_aux C L + tb_aux C L

definition cv (G : sle) : ℤ := cv_aux G.chains G.loops


open nat 

lemma cv_zero : cv empty_game = 0 := dec_trivial 

definition single_chain (c : ℕ) (Hc : c ≥ 3) : sle :=
{ chains := {c},
  chains_are_long := λ x H, begin
  rwa multiset.mem_singleton.1 H,
  end ,
  loops := ∅,
  loops_are_long_and_even := dec_trivial
}

@[simp] lemma multiset.sum_singleton {α : Type} [add_comm_monoid α]
(c : α) : multiset.sum (c :: 0) = c := begin rw multiset.sum_cons c 0,exact add_zero c end

/-
@[simp] lemma multiset.sum_singleton' {α : Type} [add_comm_monoid α]
(c : α) : multiset.sum {c} = c := multiset.sum_singleton c 
-/

lemma cv_one_chain (c : ℕ) : cv_aux (c :: 0) 0 = c :=
begin
  unfold cv_aux tb_aux,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero c,exact h.left},
  unfold fcv_aux,
  rw [multiset.sum_zero,multiset.card_zero],
  simp,ring 
end 

lemma cv_one_loop (l : ℕ) : cv_aux 0 (l :: 0) = l :=
begin
  unfold cv_aux tb_aux,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero l,exact h.2},
  { exfalso, apply multiset.singleton_ne_zero l,exact h_1},
  unfold fcv_aux,
  rw [multiset.sum_zero,multiset.card_zero],
  simp,ring
end

@[simp] lemma v_empty : value_aux 0 0 = 0 := by {rw value_aux_eq;simp}

/-
lemma multiset.pmap_singleton {α : Type} {β : Type} (c : α) (p : α → Prop) 
  (f : α → β) (h : ∀ a : α, a ∈ (c :: 0) → p a) : 
multiset.pmap (λ (a : α) (h₂ : p a), f a) (c :: 0) h = (f c :: 0) := by simp
-/

lemma v_one_chain (c : ℕ) (h : c ≥ 3) : value_aux (c :: 0) 0 = c :=
begin
  rw value_aux_eq,
  rw pmap_zero,
  rw add_zero,
  suffices : int.nat_abs 2 + (c - 2) = c,
  simp [this],
  show 2 + (c - 2) = c,
  rw add_comm,refine nat.sub_add_cancel _,
  exact le_trans (show 2 ≤ 3, by exact dec_trivial) h,
end

-- we are getting somewhere!

lemma v_one_loop (l : ℕ) (h : l ≥ 4) : value_aux 0 (l :: 0) = l :=
begin
  rw value_aux_eq,
  rw pmap_zero,
  rw zero_add,
  suffices : int.nat_abs 4 + (l - 4) = l,
  simp [this],
  show 4 + (l - 4) = l,
  rw add_comm, refine nat.sub_add_cancel _,
  assumption
end 



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

theorem multiset.card_one_iff_singleton {α : Type} {s : multiset α} : card s = 1 ↔ ∃ a, s = a::0 :=
⟨λ h,begin cases (@card_pos_iff_exists_mem _ s).1 (h.symm ▸ zero_lt_one) with a Ha,
   exact ⟨a,(eq_of_le_of_card_le (singleton_le.2 Ha) $ le_of_eq h).symm⟩ end,
 λ ⟨a,h⟩,h.symm ▸ card_singleton a⟩

-- Ellen's first lemma!
lemma one_comp_case (G : sle) : ((size G) = 1) → (cv G = value G) := 
begin
  intro H,
  have H₂ := sum_one H,
  cases H₂,
  { have H₃ : G.chains = 0 := multiset.card_eq_zero.1 H₂.left,
    have H₄ : ∃ a, G.loops = a::0 := multiset.card_one_iff_singleton.1 H₂.right,
    cases H₄ with a Ha,
    unfold value,
    unfold cv,
    rw H₃,rw Ha,
    rw cv_one_loop,
    congr,symmetry,
    refine v_one_loop a _,
    refine (sle.loops_are_long_and_even G a _).1,
    rw Ha,exact multiset.mem_singleton.2 rfl,
  },
  { have H₃ : G.loops = 0 := multiset.card_eq_zero.1 H₂.right,
    have H₄ : ∃ a, G.chains = a::0 := multiset.card_one_iff_singleton.1 H₂.left,
    cases H₄ with a Ha,
    unfold value,
    unfold cv,
    rw H₃,rw Ha,
    rw cv_one_chain,
    congr,symmetry,
    refine v_one_chain a _,
    refine (sle.chains_are_long G a _),
    rw Ha,exact multiset.mem_singleton.2 rfl,
  }
end 

--lemma loop_and_three_chain_case (G : simple_loony_endgame) : 
-- (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) → (cv_G G = value G) 

-- Ellen, this doesn't look true to me: 
#eval value_aux {3,4} {4} -- 1
#eval cv_aux {3,4} {4}  -- -1

-- lemma three_point_one (G : simple_loony_endgame) : 
-- ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  (value G ≥ 2) := sorry

-- for mathlib
#check @pmap 

lemma multiset.pmap_card (α : Type*) (β : Type*) (p : α → Prop) (H : ∀ a, p a → β) (s : multiset α) 
(H2 : ∀ a, a ∈ s → p a) : card (multiset.pmap H s H2) = card s :=
begin
  revert H2,
  apply multiset.induction_on s,finish, -- base case
  intros a s IH H3,
  rw [pmap_cons,card_cons,card_cons,IH] -- I'm a bit bewildered about why rw IH works!
end 

lemma multiset.pmap_mem {α : Type*} {β : Type*} {p : α → Prop} {H : ∀ a, p a → β} {s : multiset α} 
{H2 : ∀ a, a ∈ s → p a} {b : β} (Hb : b ∈ multiset.pmap H s H2) : ∃ a : α, ∃ Ha : a ∈ s, b = H a (H2 a Ha) :=
begin
  revert Hb,
  revert H2,
  apply multiset.induction_on s,finish,
  intros a s IH H2 Hb,
  rw pmap_cons at Hb,
  rw multiset.mem_cons at Hb,
  cases Hb,
  { existsi a,
    existsi multiset.mem_cons_self a s,
    assumption},
  have H2' : ∀ (a : α), a ∈ s → p a,
  { intros a' Ha',
    apply H2 a',
    rw multiset.mem_cons,right,assumption },
  cases (@IH H2' Hb) with a' Ha',
  existsi a',
  cases Ha' with H3 H4,
  have H5 : a' ∈ a :: s,
    rw multiset.mem_cons,right,assumption,
  existsi H5,
  assumption
end 

lemma value_ge_2_of_no_threechains_or_fourloops (G : sle) (Hpos : size G > 0) 
(Hno3chains : G.chains.count 3 = 0) (Hno4loops : G.loops.count 4 = 0) : value G ≥ 2 :=
begin
  unfold value,
  rw value_aux_eq,
  apply dots_and_boxes.N_min_ge,
  { rw [card_add,multiset.pmap_card,multiset.pmap_card],
    exact Hpos},
  intros a Ha,
  have H := mem_add.1 Ha,
  clear Ha,
  cases H,
  { have H2 := multiset.pmap_mem H,
    cases H2 with b Hb,
    cases Hb with Hb H3,
    rw H3,
    show b - 2 + int.nat_abs (2 + -↑(value_aux (erase (G.chains) b) (G.loops))) ≥ 2,
    refine le_trans _ (nat.le_add_right (b-2) _),
    apply nat.le_sub_left_of_add_le,
    have H4 : 3 ≤ b := G.chains_are_long b Hb,
    rw le_iff_eq_or_lt at H4,
    cases H4,
    { rw ←H4 at Hb, -- I now have two Hb's. Do I win £5?
      rw ←multiset.count_pos at Hb,
      rw Hno3chains at Hb,
      cases Hb
    },
    exact H4,
  },
  { have H2 := multiset.pmap_mem H,
    cases H2 with b Hb,
    cases Hb with Hb H3,
    rw H3,
    show b - 4 + int.nat_abs (4 + -↑(value_aux (G.chains) (erase (G.loops) b))) ≥ 2,
    refine le_trans _ (nat.le_add_right (b-4) _),
    apply nat.le_sub_left_of_add_le,
    have H4 := G.loops_are_long_and_even b Hb,
    cases H4 with H5 H6,
    change 4 ≤ b at H5,
    rw le_iff_eq_or_lt at H5,
    cases H5,
    { rw ←H5 at Hb, -- I now have two Hb's. Do I win £5?
      rw ←multiset.count_pos at Hb,
      rw Hno4loops at Hb,
      cases Hb
    },
    change 5 ≤ b at H5,
    rw le_iff_eq_or_lt at H5,
    cases H5,
    { rw ←H5 at H6,
      exfalso,
      revert H6,
      exact dec_trivial,
    },
    exact H5
  }
end 



/- Ellen Challenges!

lemma one_comp_case (G : simple_loony_endgame) : ((size_G G) = 1) → (cv_G G = v_G G) := sorry

lemma loop_and_three_chain_case (G : simple_loony_endgame) : (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) → (cv_G G = value G) :=
sorry

lemma three_point_one (G : simple_loony_endgame) : ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  (value G ≥ 2) := sorry


-/
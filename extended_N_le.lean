import data.multiset

def extended_le : option ℕ → option ℕ → Prop
| _ none := true
| none (some n) := false
| (some m) (some n) := m ≤ n

instance : has_le (option ℕ) := ⟨extended_le⟩

lemma none_le_none : (none : option ℕ) ≤ none := trivial

lemma some_le_none (m : ℕ) : (some m) ≤ none := trivial

lemma le_none : ∀ (a : option ℕ) , a ≤ none
| none := none_le_none
| (some m) := some_le_none m 

lemma none_not_le_some (n) : ¬ ((none : option ℕ) ≤ some n) := id 

lemma some_le_some (m n : ℕ) : (some m) ≤ (some n) → m ≤ n := id 
-- example : decidable_eq (option ℕ) := by apply_instance

lemma extended_le_refl :  ∀ (a : option ℕ), a ≤ a
| none := none_le_none
| (some m) := show m ≤ m, from le_refl m

lemma extended_le_antisymm : ∀ (a b : option ℕ), a ≤ b → b ≤ a → a = b
| none none := λ _ _,rfl
| (some m) none := λ _ H, false.elim (none_not_le_some m H)
| none (some n) := λ H _, false.elim (none_not_le_some n H)
| (some m) (some n) := λ H₁ H₂, congr_arg some (nat.le_antisymm H₁ H₂)

lemma extended_le_trans : ∀ (a b c : option ℕ), a ≤ b → b ≤ c → a ≤ c 
| _ _ none := λ _ _, le_none _
| _ none (some c) := λ _ H, false.elim (none_not_le_some c H)
| none (some b) (some c) := λ H _, false.elim (none_not_le_some b H)
| (some a) (some b) (some c) := λ H₁ H₂, nat.le_trans H₁ H₂ 

lemma extended_le_total : ∀ (a b : option ℕ), a ≤ b ∨ b ≤ a
| _ none := or.inl (le_none _)
| none _ := or.inr (le_none _)
| (some a) (some b) := nat.le_total

instance extended_decidable_le : ∀ a b : option ℕ, decidable (a ≤ b)
| none none := is_true (none_le_none)
| none (some n) := is_false (none_not_le_some n)
| (some m) none := is_true (some_le_none m)
| (some m) (some n) := match nat.decidable_le m n with 
  | is_true h := is_true h
  | is_false h := is_false h
  end

instance : decidable_linear_order (option ℕ) :=
{ le := extended_le,
  le_refl := extended_le_refl,
  le_trans := extended_le_trans,
  le_antisymm := extended_le_antisymm,
  le_total := extended_le_total,
  decidable_le := extended_decidable_le,
}

-- something of type "option ℕ" is either "some n" or "none" (which is +infinity).

#eval min (some 4) (some 7) -- some 4
#eval min (some 6) (none) -- some 6
#eval min (none) (some 12) -- some 12
#eval min (none:option ℕ) (none) -- none

-- a true "min" function on multiset (option ℕ)

def multiset.option_N_min (s : multiset (option ℕ)) : option ℕ :=
  multiset.fold (min) none s 

#eval multiset.option_N_min ↑[some 1,some 2,some 3] -- some 1
#eval multiset.option_N_min ↑[(none:option ℕ),none,none] -- none

-- the min function we want on multiset ℕ

def option_N_to_N : option ℕ → ℕ 
| none := 0
| (some n) := n

def multiset.N_min (s : multiset ℕ) : ℕ := option_N_to_N $ multiset.option_N_min $ multiset.map some s

-- the up-arrows mean "turn this list into a multiset"

#eval multiset.N_min ↑[2,3,3,2,6] -- 2
#eval multiset.N_min ↑(@list.nil ℕ) -- 0
#eval multiset.N_min ↑[6] -- 6

-- note that min of empty list is zero (because option_N_to_N sends infinity to zero)

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

definition value_aux (C : multiset ℕ) (L : multiset ℕ) : ℕ := 
begin
  revert L,
  refine multiset.strong_induction_on C _,
  intros C2 HC,
  intro L,
  refine multiset.strong_induction_on L _,
  intros L2 HL,
  refine multiset.N_min _,
  refine multiset.add _ _,
  { -- chains
    exact multiset.pmap 
      (λ a (h : a ∈ C2), a - 2 + int.nat_abs (2 - HC (C2.erase a) (multiset.erase_lt.2 h) L2))
      C2 (λ _,id),
  },
  { -- loops 
    exact multiset.pmap 
      (λ a (h : a ∈ L2), a - 4 +int.nat_abs (4 - HL (L2.erase a) (multiset.erase_lt.2 h)))
      L2 (λ _,id)
  }
end

--#check @multiset.pmap 
/-
multiset.pmap :
  Π {α : Type u_1} {β : Type u_2} {p : α → Prop},
    (Π (a : α), p a → β) → 
      Π (s : multiset α), (∀ (a : α), a ∈ s → p a) → 
        multiset β
-/
--#check @multiset.strong_induction_on 

/-
if C = ∅ then loop_value L else
multiset.strong_induction_on C 
(λ s H,multiset.N_min 
  (multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs (2 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id))
)

NO!
definition value_loop (C : multiset ℕ) (L : multiset ℕ) : ℕ := 
if L = ∅ then chain_value C else
multiset.strong_induction_on L 
(λ s H,multiset.N_min 
  (multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id))
)

definition value (G : sle') := min (value_chain G.long_chains G.long_loops) (value_loop G.long_chains G.long_loops)

-- this does not work!
-/

definition G : sle' :=
{ long_chains := {3,3,3,3,8},
  long_chains_are_long := dec_trivial,
  long_loops := {4},
  long_loops_are_long_and_even := dec_trivial
}

definition value (G : sle') := value_aux G.long_chains G.long_loops

#eval value G -- gives 0, which looks right

-- It would be easy to adapt this definition to the more complex simple loony endgame structure.

#exit 

/-
def chain_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 2 + int.nat_abs (2 - chain_value (s0.erase a))) s0 (λ a,id)

#eval chain_move_values {3,4,5,6,3,3,3,3}

def loop_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 4 + int.nat_abs (4 - loop_value (s0.erase a))) s0 (λ a,id)
-/
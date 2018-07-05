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

/-
multiset.strong_induction_on :
  Π {α : Type u_1} {p : multiset α → Sort u_2} (s : multiset α),
    (Π (s : multiset α), (Π (t : multiset α), t < s → p t) → p s) → p s

-/

-- Given a multiset s of chain lengths (each of which need to be >= 3 for this
-- function to make sense) this returns the value (to the person whose move it is not)
-- of the game.


-- #check @multiset.card_erase_of_mem 

#print multiset.strong_induction_on
/-
multiset.card_erase_of_mem :
  ∀ {α : Type u_1} [_inst_1 : decidable_eq α] {a : α} {s : multiset α},
    a ∈ s → multiset.card (multiset.erase s a) = nat.pred (multiset.card s)
-/

def chain_value : multiset ℕ → ℕ := λ s0,
multiset.strong_induction_on s0 (λ s H,multiset.N_min (multiset.map (_) s))

-- 
-- f(L) = min {a-2+|2-f(L.erase a)| for a ∈ L}

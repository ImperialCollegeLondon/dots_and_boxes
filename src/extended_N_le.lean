-- This file creates a function called dots_and_boxes.multiset.N_min which takes as input
-- a multiset of nats, and returns its min if the multiset is non-empty, and returns 0 otherwise.

import data.multiset

namespace dots_and_boxes 

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
  decidable_le := by apply_instance,
}

end dots_and_boxes

-- something of type "option ℕ" is either "some n" or "none" (which is +infinity).

#eval min (some 4) (some 7) -- some 4
#eval min (some 6) (none) -- some 6
#eval min (none) (some 12) -- some 12
#eval min (none:option ℕ) (none) -- none

-- a true "min" function on multiset (option ℕ)

-- note:
-- example : @lattice.has_inf.inf (option ℕ) _ = min := rfl 
-- so commutativity and associativity come for free

def multiset.option_N_min (s : multiset (option ℕ)) : option ℕ :=
  multiset.fold (min) none s 

#eval multiset.option_N_min ↑[some 1,some 2,some 3] -- some 1
#eval multiset.option_N_min ↑[(none:option ℕ),none,none] -- none

-- the min function we want on multiset ℕ

def dots_and_boxes.option_N_to_N : option ℕ → ℕ 
| none := 0
| (some n) := n

def multiset.N_min (s : multiset ℕ) : ℕ := dots_and_boxes.option_N_to_N $ multiset.option_N_min $ multiset.map some s

-- the up-arrows mean "turn this list into a multiset"

--#eval multiset.N_min ↑[2,3,3,2,6] -- 2
--#eval multiset.N_min ↑(@list.nil ℕ) -- 0
--#eval multiset.N_min ↑[6] -- 6

-- note that min of empty list is zero (because option_N_to_N sends infinity to zero)

namespace dots_and_boxes 

open multiset 

@[simp] lemma option_N_none : option_N_to_N none = 0 := rfl 

@[simp] lemma N_min_empty : N_min 0 = 0 := rfl 

@[simp] lemma N_min_singleton (a : ℕ) : N_min (a :: 0) = a :=
begin
  unfold N_min,simp,
  unfold option_N_min,simp,
  unfold min,rw if_pos,unfold option_N_to_N,
  unfold has_le.le,
end 

lemma option_N_min_ge (s : multiset (option ℕ)) (b : option ℕ) : (∀ a ∈ s, a ≥ b) → 
option_N_min s ≥ b := begin
  apply multiset.induction_on s,
  { -- base case
    intro H,
    show none ≥ b,
    exact le_none b
  },
  { --inductive step
    intros a s H1 H2,
    unfold option_N_min,
    rw fold_cons_left,
    apply le_min,
    { refine H2 a _,
      exact mem_cons_self _ _,
    },
    unfold option_N_min at H1,
    apply H1,
    intros a' Ha',
    apply H2,
    apply mem_cons.2,right,
    assumption
  }
end 

lemma option_N_min_eq_finite_fold (s : multiset (option ℕ)) (a : ℕ) : option_N_min (some a :: s) = multiset.fold min (some a) s :=
begin
  unfold option_N_min,
  apply fold_cons'_right,
end 

lemma option_min (x y : ℕ) : min (some x) (some y) = some (min x y) :=
begin
  unfold min,
  split_ifs;refl
end 

lemma option_N_min_eq_option_min (t : multiset ℕ) (b : ℕ) :
option_N_to_N (fold min (some b) (map some t)) = fold min b t :=
begin
  rw fold_hom min (λ x y, (option_min x y).symm),
  refl
end 

lemma fold_min (t : multiset ℕ) (a b : ℕ) : b ≤ a → (∀ c ∈ t, b ≤ c) → b ≤ fold min a t :=
begin
  intros Hba,
  apply multiset.induction_on t,finish,
  intros a' s IH H, --a' m IHba Hba c Hc Hbc,
  rw fold_cons_left,
  apply le_min,
  { apply H a',
    apply multiset.mem_cons_self},
  apply IH,
  intros c Hc,
  apply H,
  apply multiset.mem_cons.2,right,assumption
end 

lemma N_min_ge (s : multiset ℕ) (b : ℕ) (H1 : card s > 0) (H2 : ∀ a ∈ s, a ≥ b) : N_min s ≥ b := 
begin
  unfold N_min,
  have H3 := card_pos_iff_exists_mem.1 H1,
  cases H3 with a Ha,
  have H3 := exists_cons_of_mem Ha,
  cases H3 with t Ht,
  rw Ht,
  rw map_cons,
  rw option_N_min_eq_finite_fold,
  rw option_N_min_eq_option_min,
  apply fold_min,
  { apply H2,
    rw Ht,
    apply mem_cons_self
  },
  intros c Hc,
  apply H2,
  rw Ht,
  apply multiset.mem_cons.2,right,assumption
end 





end dots_and_boxes 

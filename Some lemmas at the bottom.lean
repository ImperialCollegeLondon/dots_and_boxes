import data.multiset
import order.bounded_lattice
import data.finset
open nat 

#check succ 2

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


def option_N_to_N : option ℕ → ℕ 
| none := 0
| (some n) := n

def multiset.option_N_min (s : multiset (option ℕ)) : option ℕ :=
  multiset.fold (min) none s 

def multiset.N_min (s : multiset ℕ) : ℕ := option_N_to_N $ multiset.option_N_min $ multiset.map some s

def cons_to_the_n : ℕ → ℕ →  multiset nat →  multiset nat
| 0 a b  := b
| 1 a b := (multiset.cons a b) 
| (succ n) a b := multiset.cons a (cons_to_the_n n a b) 


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

def all_chains (G : simple_loony_endgame): multiset nat :=
(cons_to_the_n G.three_chains 3 G.long_chains)

def all_loops (G : simple_loony_endgame):=
(cons_to_the_n G.four_loops 4 (cons_to_the_n G.six_loops 6 G.long_loops))

structure sle :=
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 3)
(long_loops : multiset ℕ)
(long_loops_are_long_and_even : ∀ x ∈ long_loops, x ≥ 4 ∧ 2 ∣ x)

def size_G (G : simple_loony_endgame) :=
multiset.card (simple_loony_endgame.long_loops G) + multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G


--def boardsize_G (G : simple_loony_endgame): nat := 
--(λ (a ∈  all_chains G) (b ∈ all_loops G), (a * (multiset.count a (all_chains G)) + b * (multiset.count b (all_loops G))))




--#check boardsize_G

def size (e : simple_loony_endgame) : ℕ := size_G e


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

--#eval boardsize_G empty_game

definition game_three_succ (G : simple_loony_endgame): simple_loony_endgame :=
{ three_chains := simple_loony_endgame.three_chains G + 1,
  four_loops := simple_loony_endgame.four_loops G,
  six_loops := simple_loony_endgame.six_loops G,
  long_chains := simple_loony_endgame.long_chains G,
  long_chains_are_long := simple_loony_endgame.long_chains_are_long G ,
  long_loops := simple_loony_endgame.long_loops G,
  long_loops_are_long := simple_loony_endgame.long_loops_are_long G,
  long_loops_are_even := simple_loony_endgame.long_loops_are_even G 
}


definition game_four_succ (G : simple_loony_endgame): simple_loony_endgame :=
{ three_chains := simple_loony_endgame.three_chains G,
  four_loops := simple_loony_endgame.four_loops G + 1,
  six_loops := simple_loony_endgame.six_loops G,
  long_chains := simple_loony_endgame.long_chains G,
  long_chains_are_long := simple_loony_endgame.long_chains_are_long G ,
  long_loops := simple_loony_endgame.long_loops G,
  long_loops_are_long := simple_loony_endgame.long_loops_are_long G,
  long_loops_are_even := simple_loony_endgame.long_loops_are_even G 
}


definition game_six_succ (G : simple_loony_endgame): simple_loony_endgame :=
{ three_chains := simple_loony_endgame.three_chains G,
  four_loops := simple_loony_endgame.four_loops G,
  six_loops := simple_loony_endgame.six_loops G + 1,
  long_chains := simple_loony_endgame.long_chains G,
  long_chains_are_long := simple_loony_endgame.long_chains_are_long G ,
  long_loops := simple_loony_endgame.long_loops G,
  long_loops_are_long := simple_loony_endgame.long_loops_are_long G,
  long_loops_are_even := simple_loony_endgame.long_loops_are_even G 
}


lemma add_long_all_long (α  : multiset nat) (n m : nat) : (∀ x ∈ α , x ≥ m) → (n ≥ m) → (∀ x ∈ multiset.cons n α, x ≥ m):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end

lemma add_even_all_even (α  : multiset nat) (n : nat) : (∀ x ∈ α , 2 ∣ x) → (2 ∣ n) → (∀ x ∈ multiset.cons n α, 2 ∣ x):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end

definition game_long_chain_succ (G : simple_loony_endgame) (n : nat) (Hn : n  ≥ 4 ): simple_loony_endgame :=
{ three_chains := simple_loony_endgame.three_chains G,
  four_loops := simple_loony_endgame.four_loops G,
  six_loops := simple_loony_endgame.six_loops G,
  long_chains := (multiset.cons n (simple_loony_endgame.long_chains G)) ,
  long_chains_are_long := add_long_all_long (simple_loony_endgame.long_chains G) n 4 (simple_loony_endgame.long_chains_are_long G) Hn,
  long_loops := simple_loony_endgame.long_loops G,
  long_loops_are_long := simple_loony_endgame.long_loops_are_long G,
  long_loops_are_even := simple_loony_endgame.long_loops_are_even G 
}

definition game_long_loop_succ (G : simple_loony_endgame) (n : nat) (Hn : n ≥ 8 ) (Pn : 2 ∣ n) : simple_loony_endgame :=
{ three_chains := simple_loony_endgame.three_chains G,
  four_loops := simple_loony_endgame.four_loops G,
  six_loops := simple_loony_endgame.six_loops G,
  long_chains := simple_loony_endgame.long_chains G,
  long_chains_are_long := simple_loony_endgame.long_chains_are_long G ,
  long_loops := multiset.cons n (simple_loony_endgame.long_loops G) ,
  long_loops_are_long := add_long_all_long (simple_loony_endgame.long_loops G) n 8 (simple_loony_endgame.long_loops_are_long G) Hn,
  long_loops_are_even := add_even_all_even (simple_loony_endgame.long_loops G) n (simple_loony_endgame.long_loops_are_even G) Pn 
}

def chain_value (sc : multiset ℕ) : ℕ := multiset.strong_induction_on sc $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs (2 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval (chain_value {4,5,6}) -- 7
#eval chain_value {3,3,3,3,3,3,3,3}

def loop_value (s0 : multiset ℕ) : ℕ := multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval loop_value {4,4,4,4}

def chain_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 2 + int.nat_abs (2 - chain_value (s0.erase a))) s0 (λ a,id)

#eval chain_move_values {3,4,5,6,3,3,3,3}

def loop_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 4 + int.nat_abs (4 - loop_value (s0.erase a))) s0 (λ a,id)

definition value (G : simple_loony_endgame) := multiset.N_min (chain_move_values (all_chains G) + loop_move_values (all_loops G))

def legal_moves (e : simple_loony_endgame) : finset {f : simple_loony_endgame // size f < size e} := 
sorry

def val : simple_loony_endgame → with_top ℕ
| e := (legal_moves e).inf
  (λ f, have size f.1 < size e := f.2, (val f.1 : with_top ℕ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf size⟩]}

def distel (m : multiset nat): nat := multiset.card (multiset.erase_dup (m))

def fcv_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G) 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_chains G)) + 1)*4 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_loops G)) + 2)*8 

def tb_G (G : simple_loony_endgame)  :=
if size_G G = 0 then 0
else if multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (simple_loony_endgame.long_loops G) + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G = 0 then 4
else if simple_loony_endgame.long_chains G = multiset.zero then 6
else 4

#check game_three_succ empty_game

#check game_long_loop_succ empty_game 8 

#check min 1 2

def v_G (G : simple_loony_endgame) := fcv_G G + tb_G G

def cv_G (G : simple_loony_endgame) := fcv_G G + tb_G G

---------------------------------------------------------------------------------------------------------------
--------------------------------------------------theorems-----------------------------------------------------

lemma one_comp_case (G : simple_loony_endgame) : ((size_G G) = 1) → (cv_G G = v_G G) := sorry

lemma loop_and_three_chain_case (G : simple_loony_endgame) : (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) → (cv_G G = value G) :=
sorry

lemma three_point_one (G : simple_loony_endgame) : ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  (value G ≥ 2) := sorry

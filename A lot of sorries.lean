import data.multiset
import order.bounded_lattice
import data.finset
import extended_N_le tactic.ring
import init.algebra.functions
import data.int.basic
import logic.basic

open nat 

------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------- functions on multisets ----------------------------------------------------------

def cons_to_the_n : ℕ → ℕ →  multiset nat →  multiset nat
| 0 a b  := b
| 1 a b := (multiset.cons a b) 
| (succ n) a b := multiset.cons a (cons_to_the_n n a b) 


lemma cons_to_the_next_n (x n d : nat) ( α : multiset nat) : x ∈  cons_to_the_n n d α →  x ∈  cons_to_the_n (succ n) d α :=
begin
intro a, have h : x ∈ multiset.cons d (cons_to_the_n n d α), simp, right, by exact a, induction n with t Ht, unfold cons_to_the_n ,
unfold cons_to_the_n at a, rw multiset.mem_cons, right, by exact a, unfold cons_to_the_n, by exact h , 
end

lemma cons_to_the_prev_n (x t z : nat) (α : multiset nat) : x ∈ cons_to_the_n (succ t) z α → x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z :=
begin
intro a, induction t with p Hp, left, simp, unfold cons_to_the_n, unfold cons_to_the_n at a, finish, 
left, unfold cons_to_the_n at a, by exact a
end




lemma lenpre (x y z m : nat)(α : multiset nat) : (z ≥ y) → (∀ x ∈ α, x ≥ y) → (x ∈ cons_to_the_n m z α →  x ≥ y) :=
begin
intros M Q H, induction m with t Pt, unfold cons_to_the_n at H, finish, 
have Hn :  x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z,
 by exact cons_to_the_prev_n x t z α H, 
rw[multiset.mem_cons] at Hn, cases Hn, cases Hn, finish,  exact Pt Hn, rw Hn, finish
end

lemma still_even (x z n : nat) (α : multiset nat) : (2 ∣ z) → (∀ x ∈ α, 2 ∣ x) → (x ∈ cons_to_the_n n z α →  2 ∣ x) :=
begin
intros H P Q, induction n with t Ht, unfold cons_to_the_n at Q, finish,  
have Hn :  x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z,
 by exact cons_to_the_prev_n x t z α Q, 
rw[multiset.mem_cons] at Hn, cases Hn, cases Hn, rw Hn, exact H, exact Ht Hn, rw Hn, exact H,
end

lemma new (a b c : nat) : a ≥ b → b ≥ c → a ≥ c :=
begin intros x y, by exact ge_trans x y,
end  


def distel (m : multiset nat): nat := multiset.card (multiset.erase_dup (m))

lemma add_long_all_long (α  : multiset nat) (n m : nat) : (∀ x ∈ α , x ≥ m) → (n ≥ m) → (∀ x ∈ multiset.cons n α, x ≥ m):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end

lemma add_even_all_even (α  : multiset nat) (n : nat) : (∀ x ∈ α , 2 ∣ x) → (2 ∣ n) → (∀ x ∈ multiset.cons n α, 2 ∣ x):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end




-------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------- simple_loony_endgame -------------------------------------------------------

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

lemma now (m : multiset nat) ( a b : nat) : a ≥ b →  (∀ x ∈ m, x ≥ a) → (∀ x ∈ m, x ≥ b) := 
begin intros c d e f , have H : e ≥ a, by exact d e f,  exact ge_trans H c 
end



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


--------------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------------- sle -------------------------------------------------------------

structure sle :=
(chains : multiset ℕ)
(chains_are_long : ∀ x ∈ chains, x ≥ 3)
(loops : multiset ℕ)
(loops_are_long_and_even : ∀ x ∈ loops, x ≥ 4 ∧ 2 ∣ x)


definition empty_game_sle : sle := {chains := ∅,chains_are_long := dec_trivial, 
  loops := ∅, loops_are_long_and_even := dec_trivial}


def all_chains (G : simple_loony_endgame): multiset nat :=
(cons_to_the_n G.three_chains 3 G.long_chains)

def all_loops (G : simple_loony_endgame):=
(cons_to_the_n G.four_loops 4 (cons_to_the_n G.six_loops 6 G.long_loops))

def simple_loony_endgame_to_sle (G : simple_loony_endgame) : sle :=
{
  chains := (all_chains G),
  chains_are_long := begin intros, unfold all_chains at H, have P : 3 ≥ 3 , finish, have K : 4 ≥ 3, by exact dec_trivial, 
  have Q : ∀ x ∈ G.long_chains, x ≥ 4, by exact G.long_chains_are_long, have R : (∀ x ∈ G.long_chains, x ≥ 3),
  exact now G.long_chains 4 3 K Q,  exact lenpre x 3 3 G.three_chains G.long_chains P R H, end,
  loops := (all_loops G),
  loops_are_long_and_even := begin intros x y, unfold all_loops at y, split,
  have P : 6 ≥ 4 , exact dec_trivial, have K : 8 ≥ 4, by exact dec_trivial, have L : 4 ≥ 4, exact dec_trivial, have Q : ∀ x ∈ G.long_loops,
  x ≥ 8, by exact G.long_loops_are_long, have R : (∀ x ∈ G.long_loops, x ≥ 4), exact now G.long_loops 8 4 K Q, let α := cons_to_the_n (G.six_loops) 
  6 (G.long_loops), have z : x ∈ cons_to_the_n (G.four_loops) 4 α, finish, have S : ∀ x ∈ α , x ≥ 4 , intros m n, 
  exact lenpre m 4 6 G.six_loops G.long_loops P R n, exact  lenpre x 4 4 G.four_loops α L S y,
  have P : 2 ∣ 4 , exact dec_trivial, have K : 2 ∣ 6, by exact dec_trivial,  have Q : ∀ x ∈ G.long_loops,
  2 ∣ x, by exact G.long_loops_are_even, let α := cons_to_the_n (G.six_loops) 6 (G.long_loops), have z : x ∈ cons_to_the_n (G.four_loops) 4 α,
  finish, have S : ∀ x ∈ α , 2 ∣ x , intros m n, exact still_even m 6 G.six_loops G.long_loops K Q n, 
  exact still_even x 4 G.four_loops α P S y,
  end 
}

def sle_to_simple_loony_endgame (G : sle) : simple_loony_endgame :=
{ three_chains := multiset.count 3 G.chains,
  four_loops := multiset.count 4 G.loops,
  six_loops := multiset.count 6 G.loops,
  long_chains := multiset.filter (λ x, x ≥ 4) G.chains, 
  long_chains_are_long := begin intros a b, rw multiset.mem_filter at b, exact b.right end,
  long_loops := multiset.filter (λ x, x ≥ 8) G.loops, 
  long_loops_are_long := begin intros a b, rw multiset.mem_filter at b, exact b.right end,
  long_loops_are_even := begin intros a b, rw multiset.mem_filter at b, cases b, exact and.right (G.loops_are_long_and_even a b_left) end
}


 
def rem_chain_from_sle (G : sle) (a:nat) : sle :=
{
  chains := (multiset.erase (sle.chains G) a),
  chains_are_long := begin intros, have H2 : (x ∈ G.chains), by exact multiset.mem_of_mem_erase H,
  clear H, have H1 : ∀ x ∈ G.chains, x ≥ 3, by exact G.chains_are_long, finish, end,
  loops := (sle.loops G),
  loops_are_long_and_even := G.loops_are_long_and_even
}


def rem_loop_from_sle (G : sle) (a:nat) : sle :=
{
  chains := (sle.chains G),
  chains_are_long := G.chains_are_long,
  loops := (multiset.erase (sle.loops G) a),
  loops_are_long_and_even := begin intros, split, have H1 : (x ∈ G.loops),
  by exact multiset.mem_of_mem_erase H, have H2 : ∀ x ∈ G.loops, x ≥ 4 ∧ 2 ∣ x,  by exact G.loops_are_long_and_even,
   finish, have H1 : (x ∈ G.loops),
  by exact multiset.mem_of_mem_erase H, have H2 : ∀ x ∈ G.loops, x ≥ 4 ∧ 2 ∣ x,  by exact G.loops_are_long_and_even,
   finish, end
} 


def cons_chain_to_sle (G : sle) (a:nat) (Ha : a ≥ 3 ) : sle :=
{
  chains := (multiset.cons a (sle.chains G)),
  chains_are_long := add_long_all_long (sle.chains G) a 3 (sle.chains_are_long G) Ha,
  loops := (sle.loops G),
  loops_are_long_and_even := G.loops_are_long_and_even
}


def cons_loop_to_sle (G : sle) (a:nat) (Ha : a ≥ 4 ) (Pa : 2 ∣ a) : sle :=
{
  chains := (sle.chains G),
  chains_are_long := G.chains_are_long,
  loops := (multiset.cons a (sle.loops G)),
  loops_are_long_and_even := begin intros, split,  rw[multiset.mem_cons] at H, cases H, rw H, by exact Ha, 
   have P : x ≥ 4, by exact and.left (sle.loops_are_long_and_even G x H), by exact P,
  rw multiset.mem_cons at H, cases H, rw H, by exact Pa,  have P : 2 ∣ x, by exact and.right (sle.loops_are_long_and_even G x H), by exact P,
  end
} 

--------------------------------------------------------------------------------------------------------------------------------------
------------------------------------------ functions on simple_loony_endgame and sle -------------------------------------------------



lemma rem_chain_eq_zero_to_singleton (G : sle) (c : nat) (c ∈ G.chains) : (rem_chain_from_sle G c).chains = 0 → G.chains = c :: 0 :=
begin
unfold rem_chain_from_sle, simp, intro x,
rw ← multiset.cons_erase H, rw x,  
end

lemma rem_chain_eq_zero_of_singleton (G : sle) (c : nat) (c ∈ G.chains) :  G.chains = c :: 0 → (rem_chain_from_sle G c).chains = 0:=
begin
unfold rem_chain_from_sle, simp, intro x,
rw ← multiset.cons_erase H, rw x,  simp, 
end

lemma rem_loop_eq_zero_to_singleton (G : sle) (c : nat) (c ∈ G.loops) : (rem_loop_from_sle G c).loops = 0 → G.loops = c :: 0 :=
begin
unfold rem_loop_from_sle, simp, intro x,
rw ← multiset.cons_erase H, rw x,  
end

lemma rem_loop_eq_zero_of_singleton (G : sle) (c : nat) (c ∈ G.loops) : G.loops = c :: 0 → (rem_loop_from_sle G c).loops = 0 :=
begin
unfold rem_loop_from_sle, simp, intro x,
rw ← multiset.cons_erase H, rw x, simp 
end

def size_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G)

definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

def size (e : sle) : ℕ := multiset.card e.chains + multiset.card e.loops

lemma zero_sum (a b : nat) : a + b = 0 → a = 0 ∧ b = 0 := begin intro x, split, induction b with t Ht,
  rw ← x, simp, exfalso, rw add_succ at x, finish, induction a with t Ht,
  rw ← x, simp, exfalso, rw succ_add at x, finish,  end 

lemma zero_size (G : sle) : size G = 0 → G.chains = 0 ∧ G.loops = 0 :=
begin
intro x, dunfold size at x, have y : multiset.card G.chains = 0 ∧ multiset.card G.loops = 0, by exact zero_sum (multiset.card G.chains) 
(multiset.card G.loops) x, split,
cases y, rw ← multiset.card_eq_zero,  exact y_left, cases y, rw ← multiset.card_eq_zero,  exact y_right,
end

lemma empty_game_iff_size_zero (G : sle) : G = empty_game_sle ↔ size G = 0 :=
begin
split, 
intro x, rw x, dunfold size, unfold empty_game_sle, simp, 
show multiset.card 0 + multiset.card 0 = 0, simp, 
intro x, unfold empty_game_sle, show G =
    {chains := 0,
     chains_are_long := empty_game_sle._proof_1,
     loops := 0,
     loops_are_long_and_even := empty_game_sle._proof_2},

sorry,
end

def squnum_G (G : simple_loony_endgame): nat := 
multiset.fold (nat.add) 0 (all_chains G) + multiset.fold (nat.add) 0 (all_loops G)

def squnum (G : sle): nat := 
multiset.fold (nat.add) 0 (G.chains) + multiset.fold (nat.add) 0 (G.loops)



def chain_value (s0 : multiset ℕ) : ℕ := 
multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs 
(2 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval (chain_value {4,5,6}) -- 7
#eval chain_value {3,3,3,3,3,3,3,3}

def loop_value (s0 : multiset ℕ) : ℕ := multiset.strong_induction_on s0 $ λ s H,multiset.N_min $ multiset.pmap
  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id)

#eval loop_value {4,4,4,4}

def chain_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 2 + int.nat_abs (2 - chain_value (s0.erase a))) s0 (λ a,id)

def loop_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 4 + int.nat_abs (4 - loop_value (s0.erase a))) s0 (λ a,id)



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


/-definition value_aux (C : multiset ℕ) : multiset ℕ → ℕ := 
  multiset.strong_induction_on C (λ C2 HC L,(
    multiset.strong_induction_on L (λ L2 HL,
      multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C2), a - 2 + int.nat_abs (2 - HC (C2.erase a) (multiset.erase_lt.2 h) L2))
      C2 (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L2), a - 4 +int.nat_abs (4 - HL (L2.erase a) (multiset.erase_lt.2 h)))
      L2 (λ _,id))
    )
  ))

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

definition value_G (G : simple_loony_endgame) := value_aux (all_chains G) (all_loops G)

definition value (G : sle) := value_aux G.chains G.loops



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
+if C = ∅ then loop_value L else
+multiset.strong_induction_on C 
+(λ s H,multiset.N_min 
+  (multiset.pmap
+  (λ (a : ℕ) (h : a ∈ s),a - 2 + int.nat_abs (2 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id))
+)
+
+NO!
+definition value_loop (C : multiset ℕ) (L : multiset ℕ) : ℕ := 
+if L = ∅ then chain_value C else
+multiset.strong_induction_on L 
+(λ s H,multiset.N_min 
+  (multiset.pmap
+  (λ (a : ℕ) (h : a ∈ s),a - 4 + int.nat_abs (4 - H (s.erase a) (multiset.erase_lt.2 h))) s (λ a, id))
+)
+
+definition value (G : sle') := min (value_chain G.long_chains G.long_loops) (value_loop G.long_chains G.long_loops)
+
+-- this does not work!
+-/





def fcv_G (G : simple_loony_endgame): int :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + int.of_nat (multiset.sum (simple_loony_endgame.long_loops G) )
+ int.of_nat (multiset.sum (simple_loony_endgame.long_chains G)) 
- (multiset.card (simple_loony_endgame.long_chains G) + 1)*4 
- (multiset.card (simple_loony_endgame.long_loops G) + 2)*8 

def fcv (G : sle):= int.of_nat (multiset.sum G.chains) + int.of_nat (multiset.sum G.loops) - (multiset.card (G.chains))*4 
- (multiset.card (G.loops))*8 

lemma fcv_rem_chain (G : sle) (c ∈ G.chains) : fcv (rem_chain_from_sle G c) =  int.of_nat (multiset.sum (multiset.erase G.chains c)) 
+ int.of_nat (multiset.sum G.loops) - (multiset.card ((multiset.erase G.chains c)))*4 - (multiset.card (G.loops))*8 :=
begin
unfold rem_chain_from_sle, unfold fcv, 
end


lemma fcv_rem_loop (G : sle) (c ∈ G.loops) : fcv (rem_loop_from_sle G c) =  int.of_nat (multiset.sum G.chains) 
+ int.of_nat (multiset.sum (multiset.erase G.loops c)) - (multiset.card (G.chains))*4 - (multiset.card (multiset.erase G.loops c))*8 := 
begin
unfold rem_loop_from_sle, unfold fcv, 
end



definition fcv_aux (C L : multiset ℕ) : ℤ := ↑(multiset.sum C + multiset.sum L) 
  - 4 * multiset.card C - 8 * multiset.card L

definition fcv_KB (G : sle) : ℤ := fcv_aux G.chains G.loops



-- Chris and Simon decidability thing
instance decidable_exists_multiset {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) := quotient.rec_on s
list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

instance (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ 4),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

def tb_G (G : simple_loony_endgame)  :=
if size_G G = 0 then 0
else if multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (simple_loony_endgame.long_loops G) + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G = 0 then 4
else if simple_loony_endgame.long_chains G = multiset.zero then 6
else 4

-- without those 6 lines of gobble-de-gook above, the below lines don't work
definition tb_aux (C L : multiset ℕ) : ℕ := if (C = 0 ∧ L = 0) then 0 else
  if L = 0 then 4 else
  if C = 0 then 8 else
  if ∃ a : ℕ, a ≥ 4 ∧ a ∈ C then 4 else 
  6

def tb (G : sle)  :=
if size G = 0 then 0
else if  G.loops = 0 then 4
else if  G.chains = 0 then 8
--else if (multiset.count 3 G.long_chains) = (multiset.card G.long_chains) then 6
else if multiset.erase_dup (G.chains) = (multiset.cons 3 0) then 6
else 4

lemma working_title (G : sle) (c : nat) (c ∈ G.chains) : multiset.erase_dup (multiset.erase (G.chains) c) = 3 :: 0
→  G.chains = c :: multiset.filter (λ (x : ℕ), x = 3) (G.chains) :=
begin
intro h, sorry
end


lemma tb_rem_chain (G : sle) (c : nat) (Hc : c ∈ G.chains ) : tb (rem_chain_from_sle G c) =
if G.chains = c :: 0 ∧ G.loops = 0 then 0
else if G.loops = 0 then 4
else if G.chains = c :: 0  then 8
else if G.chains = multiset.cons c (multiset.filter (λ x, x = 3) G.chains) ∨ multiset.erase_dup G.chains = (multiset.cons 3 0) then 6
else 4 :=
begin
unfold tb,
split_ifs, 
refl,
exfalso, have l : (rem_chain_from_sle G c).chains = 0, exact (zero_size (rem_chain_from_sle G c) h).left, 
rw [rem_chain_eq_zero_to_singleton G c c Hc l] at h_1, rw h_2 at h_1, finish,
exfalso, have l : (rem_chain_from_sle G c).loops = 0, exact (zero_size (rem_chain_from_sle G c) h).right,
unfold rem_chain_from_sle at l, simp at l,  finish,
exfalso, have l : (rem_chain_from_sle G c).loops = 0, exact (zero_size (rem_chain_from_sle G c) h).right,
unfold rem_chain_from_sle at l, simp at l,  finish,
exfalso, have l : (rem_chain_from_sle G c).loops = 0, exact (zero_size (rem_chain_from_sle G c) h).right,
unfold rem_chain_from_sle at l, simp at l,  finish,
exfalso, dunfold size at h, rw h_1 at h, unfold rem_chain_from_sle at h, simp at h, rw h_2.left at h, finish, 
refl,
exfalso, unfold rem_chain_from_sle at h_1, rw h_3.right at h_1, simp at h_1, exact h_1,
refl,
exfalso, rw rem_chain_eq_zero_to_singleton G c c Hc h_2 at h_4, finish,
exfalso, rw rem_chain_eq_zero_to_singleton G c c Hc h_2 at h_4, finish, 
exfalso, unfold rem_chain_from_sle at h_1, rw h_4.right at h_1, simp at h_1, exact h_1,
exfalso, unfold rem_chain_from_sle at h_2, simp at h_2, rw h_5 at h_2, finish,
refl,
exfalso, rw not_or_distrib at h_6, have p : G.chains = c :: multiset.filter (λ (x : ℕ), x = 3) (G.chains),
unfold rem_chain_from_sle at h_3, simp at h_3, exact working_title G c c Hc h_3, finish,  --rw h_3 at h_6, finish, sorry,
exfalso, unfold rem_chain_from_sle at h_2, simp at h_2, rw h_4.left at h_2, finish,
exfalso, rw rem_chain_eq_zero_of_singleton G c c Hc h_5 at h_2, finish, 
exfalso, have p : multiset.erase_dup ((rem_chain_from_sle G c).chains) = 3 :: 0,
unfold rem_chain_from_sle, simp, cases h_6, 
rw h_6, simp,  sorry,
  sorry,
finish,
refl,
end

lemma tb_rem_loop (G : sle) (c : nat) (Hc : c ∈ G.loops ) : tb (rem_loop_from_sle G c) =
if G.chains = 0 ∧ G.loops = c :: 0 then 0
else if G.chains = 0 then 8
else if G.loops = c :: 0  then 4
else if multiset.erase_dup (G.chains) = (multiset.cons 3 0) then 6
else 4 := 
begin
unfold tb,
split_ifs, 
refl,
exfalso, have l : (rem_loop_from_sle G c).loops = 0, exact (zero_size (rem_loop_from_sle G c) h).right, 
rw [rem_loop_eq_zero_to_singleton G c c Hc l] at h_1, rw h_2 at h_1, finish,
exfalso, have l : (rem_loop_from_sle G c).chains = 0, exact (zero_size (rem_loop_from_sle G c) h).left,
unfold rem_loop_from_sle at l, simp at l,  finish,
exfalso, have l : (rem_loop_from_sle G c).chains = 0, exact (zero_size (rem_loop_from_sle G c) h).left,
unfold rem_loop_from_sle at l, simp at l,  finish,
exfalso, have l : (rem_loop_from_sle G c).chains = 0, exact (zero_size (rem_loop_from_sle G c) h).left,
unfold rem_loop_from_sle at l, simp at l,  finish,
exfalso, dunfold size at h, rw h_1 at h, unfold rem_loop_from_sle at h, simp at h, rw h_2.left at h, finish, 
exfalso, rw rem_loop_eq_zero_to_singleton G c c Hc h_1 at h_2, rw h_3 at h_2, finish,
refl,
exfalso, rw rem_loop_eq_zero_to_singleton G c c Hc h_1 at h_4, finish,
refl,
exfalso, rw rem_loop_eq_zero_of_singleton G c c Hc h_3.right at h_1, finish,
refl, 
exfalso, unfold rem_loop_from_sle at h_1, simp at h_1, rw h_4.right at h_1, finish,
exfalso, rw rem_loop_eq_zero_of_singleton G c c Hc h_5 at h_1, finish,  
refl,
exfalso, rw rem_loop_eq_zero_of_singleton G c c Hc h_4.right at h_1, finish, 
exfalso, rw rem_loop_eq_zero_of_singleton G c c Hc h_5 at h_1, finish, 
refl,
end

def cv_G (G : simple_loony_endgame) : int := fcv_G G + tb_G G

definition cv_aux (C L : multiset ℕ) : ℤ := fcv_aux C L + tb_aux C L

def cv (G : sle): int := fcv G + tb G

lemma cv_zero : cv empty_game_sle = 0 := dec_trivial 

def G_is_even (G : sle) := 2 ∣ cv G ∧ 2 ∣ value G ∧ 2 ∣ size G  

def loop_move_is_optimal_G (G : simple_loony_endgame) (a: nat): Prop  :=
value_G G = a - 4 + int.nat_abs (4 - value_aux (all_chains G) ((all_loops G).erase a))

def loop_move_is_optimal (G : sle) (a: nat): Prop  :=
value G = a - 4 + int.nat_abs (4 - value_aux (G.chains) ((G.loops).erase a))

def chain_move_is_optimal_G (G : simple_loony_endgame) (a: nat): Prop  :=
value_G G = a - 2 + int.nat_abs (2 - value_aux ((all_chains G).erase a) (all_loops G))

def chain_move_is_optimal (G : sle) (a: nat): Prop  :=
value G = a - 2 + int.nat_abs (2 - value_aux ((G.chains).erase a) (G.loops))

def open_chain_ok (G : sle) (a: nat): Prop  := sorry

def open_loop_ok (G : sle) (a: nat): Prop  := sorry

def v_of_G_with_chain (G : sle) (c : nat) := c - 2 + int.nat_abs (2 - ↑(value_aux ((G.chains).erase c) (G.loops)))

def v_of_G_with_loop (G : sle) (l : nat) := l - 4 + int.nat_abs (4 - ↑(value_aux (G.chains) ((G.loops).erase l)))

def one_one_ab (G : sle) := rem_loop_from_sle (rem_chain_from_sle G 3) 4

def one_one_c (G : sle) := rem_loop_from_sle (rem_chain_from_sle (rem_chain_from_sle G 3) 3) 4

def exceptions (G : sle): Prop := 
(3 ∈ G.chains ∧ 4 ∈ G.loops ∧ 4 ∣ (size (one_one_ab G)) ∧ 3 ∉ (one_one_ab G).chains)
∨ (3 ∈ G.chains ∧ 4 ∈ G.loops ∧ cv G = 0 ∧ ((∃ c ∈ (one_one_ab G).chains, c ≥ 4) ∨ (∃ c ∈ (one_one_ab G).loops, c ≥ 4)))
∨ (multiset.count 3 G.chains ≥ 2 ∧ 4 ∈ G.loops ∧ cv G = -1 ∧ ((∃ c ∈ (one_one_c G).chains, c ≥ 4) ∨ (∃ c ∈ (one_one_c G).loops, c ≥ 4)))
∨ (G.chains = 3 :: 0 ∧ G.loops ≠ 0 ∧ cv G ≥ 2)

/-def Defender_Strategy (G : sle) (H : G ≠ empty_game_sle) := 
if 3 ∈ G.chains ∧  ¬ (exceptions G) then chain_move_is_optimal G 3
else if G.loops ≠ 0 then loop_move_is_optimal G (multiset.N_min G.loops)
else chain_move_is_optimal G (multiset.N_min G.chains)
-/

def Keep_Control_loop (G : sle) (c : nat):=
if cv (rem_loop_from_sle G c) > 4 then true else false

def Keep_Control_chain (G : sle) (c : nat):=
if cv (rem_chain_from_sle G c) > 2 then true else false

def Strategy_when_cv_ge_2_defender (G : sle) (H : cv G ≥ 2) :=
if 3 ∈ G.chains ∧ G.chains ≠ 3 :: 0 then open_chain_ok G 3
else if 4 ∈ G.loops then open_loop_ok G 4
else if 6 ∈ G.loops then open_loop_ok G 6
else if G.loops ≠ 0 then ∀ c ∈ G.loops, open_loop_ok G c
else ∀ c ∈ G.chains, open_chain_ok G c

lemma v_of_G_with_chain_imp (G : sle) ( x : nat) : x ∈ G.chains →  v_of_G_with_chain G x ≥ (x - 2) :=
begin
intro a, unfold v_of_G_with_chain, induction int.nat_abs (2 - ↑(value_aux (multiset.erase (G.chains) x) (G.loops)))  with t Ht,
rw add_zero, finish,  have P : x - 2 + succ t ≥ x - 2 + t, rw succ_eq_add_one, rw ← add_assoc, 
show x - 2 + t ≤ x - 2 + t + 1, rw le_add_one_iff, left, finish, 
 exact ge_trans P Ht,
end

lemma v_of_G_with_loop_imp (G : sle) ( x : nat) : x ∈ G.loops →  v_of_G_with_loop G x ≥ (x - 4) :=
begin
intro a, unfold v_of_G_with_loop, induction int.nat_abs (4 - ↑(value_aux (G.chains) ((G.loops).erase x)))  with t Ht,
rw add_zero, finish,  have P : x - 4 + succ t ≥ x - 4 + t, rw succ_eq_add_one, rw ← add_assoc, 
show x - 4 + t ≤ x - 4 + t + 1, rw le_add_one_iff, left, finish, 
 exact ge_trans P Ht,
end

@[simp] lemma v_empty : value_aux 0 0 = 0 := by {rw value_aux_eq, simp }

lemma v_of_empty_game (G : sle) : G = empty_game_sle → value G = 0 := 
begin 
intro x, rw x, unfold empty_game_sle, 
show value
      {chains := 0,
       chains_are_long := empty_game_sle._proof_1,
       loops := 0,
       loops_are_long_and_even := empty_game_sle._proof_2} =
    0,
 unfold value, 
simp,
end



#check le_sub_left_of_add_le

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

namespace multiset 

theorem repeat_one {α : Type*} {a : α} : repeat a 1 = a :: 0 :=
(eq_repeat'.2 (λ b,mem_singleton.1 : ∀ b ∈ a :: 0, b = a)).symm

@[simp] theorem erase_dup_singleton {α : Type*} [decidable_eq α] {a : α} : erase_dup (a :: 0) = a :: 0 :=
  erase_dup_cons_of_not_mem $ not_mem_zero a

end multiset

-- proof starts here
open multiset 

lemma loop468 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
∀ l ∈ L, l = 4 ∨ l = 6 ∨ l ≥ 8 :=
begin
  intros l Hl,
  have H := HL l Hl,clear HL,clear Hl,
  cases H with Hl He,
  cases eq_or_lt_of_le Hl with H4 H4,
    left,exact H4.symm,
  change 5 ≤ l at H4,
  cases eq_or_lt_of_le H4 with H5 H5,
    exfalso, revert He,rw ←H5,exact dec_trivial,
  clear H4,change 6 ≤ l at H5,
  cases eq_or_lt_of_le H5 with H6 H6,
    right,left,exact H6.symm,
  clear H5,change 7 ≤ l at H6,
  cases eq_or_lt_of_le H6 with H7 H7,
    exfalso,revert He,rw ←H7,exact dec_trivial,
  right,right,exact H7
end 



lemma cases_for_C (C : multiset ℕ) (HC : ∀ x ∈ C, x ≥ 3) :
  C = 0 
∨ C = 3 :: 0 
∨ (∃ n : ℕ, n ≥ 2 ∧ C = repeat 3 n) 
∨ (3 ∈ C ∧ ∃ c : ℕ, c ≥ 4 ∧ c ∈ C) 
∨ (3 ∉ C ∧ ∃ c : ℕ, c ≥ 4 ∧ c ∈ C)
:= begin
  /- If the next line gives error
  by_cases tactic failed, type of given expression is not decidable
  then your mathlib needs updating because Chris fixed this a couple of weeks ago
  -/
  by_cases H4 : (∃ c ∈ C, c ≥ 4), 
  { by_cases H3 : (3 ∈ C),
      right,right,right,left,split,assumption,
        cases H4 with c Hc,existsi c,cases Hc with Hc1 Hc2,exact ⟨Hc2,Hc1⟩,
      right,right,right,right,split,assumption,
        cases H4 with c Hc,existsi c,cases Hc with Hc1 Hc2,exact ⟨Hc2,Hc1⟩,
  },
  have H3 : ∀ c ∈ C, c = 3,
    intros c Hc,
    cases (eq_or_lt_of_le $ HC c Hc) with H H,
      exact H.symm,
      exfalso,apply H4,existsi c,existsi Hc,exact H,
  have Hrep := eq_repeat'.2 H3,
  cases H : C.card,
    left,rwa ←card_eq_zero,
  cases n with d Hd,
    right,left,
    rw [Hrep,H,repeat_one],
  right,right,left,
  existsi d+2,
  split,exact nat.le_add_left 2 d,
  rw Hrep,rw H
end 

-- C is empty
-- 3 ∉ C ∧ ∃ c, c ≥ 4 ∧ c ∈ C 
lemma cases_for_L1 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
  L = 0
∨ ¬ (L = 0) ∧ 4 ∉ L ∧ 6 ∉ L
∨ 4 ∈ L 
∨ 6 ∈ L 
:= begin
  by_cases H : (L = 0),
    left,assumption,
  by_cases H4 : 4 ∈ L,
    right,right,left,assumption,
  by_cases H6 : 6 ∈ L,
    right,right,right,assumption,
  right,left,split,assumption,split;assumption
end

-- C = {3}
lemma cases_for_L2 (L : multiset ℕ) (HL : ∀ x ∈ L, x ≥ 4 ∧ 2 ∣ x) :
  (4 ∉ L ∧ 6 ∉ L)
∨ ((4 ∈ L ∨ 6 ∈ L) ∧ card L ≥ 2)
∨ card L = 1
:= begin
  cases H : card L,
    left,rw card_eq_zero at H,rw H,simp,
  cases n with d,
    right,right,refl,
  by_cases H4 : 4 ∈ L,
    right,left,split,left,assumption,exact dec_trivial,
    by_cases H6 : 6 ∈ L,
      right,left,split,right,assumption,exact dec_trivial,
      left,exact ⟨H4,H6⟩
end 

 

lemma exhaustive_cases (G : sle) :
  (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 )
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2) :=
begin
  have HC := cases_for_C G.chains G.chains_are_long,
  cases HC,
  { -- C empty
    have HL := cases_for_L1 G.loops G.loops_are_long_and_even,
    cases HL,
    { right,left,rw HC,rw HL,split,refl,refl
    },
    cases HL,
    { right,right,left,rw HC,split,refl,
      split,swap,exact HL.1,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.2.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2.2,rwa ←H2,
      exact H2,
    },
    right,right,right,right,right,right,left,split,
      exact HL,
      exact HC
  },
  cases HC,
  { -- C = {3}
    have HL := cases_for_L2 G.loops G.loops_are_long_and_even,
    cases HL,
    { right,right,right,left,
      split,exact HC,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2,rwa ←H2,
      exact H2,
    },
    cases HL,
    { right,right,right,right,right,right,right,
      split,exact HL.1,
      split,exact HC,
      exact HL.2
    },
    { left,
      exact ⟨HC,HL⟩
    }
  },
  cases HC,
  { -- C={3,3,...,3}
    cases HC with n Hn,cases Hn with Hn HC,
    right,right,right,right,right,left,
    split,rw HC,rw [count_repeat],exact Hn,
    rw [HC],rw ←erase_dup_singleton,
    rw erase_dup_ext,intro l,split,
      intro H,rw (eq_of_mem_repeat H),rw mem_singleton,
    intro H,rw mem_singleton at H,rw H,rw [←count_pos,count_repeat],
      exact lt_of_lt_of_le dec_trivial Hn
  },
  cases HC,
  { -- 3 ∈ C ∧ ∃ c >= 4, c ∈ C
    right,right,right,right,left,
    split,left,exact HC.1,
    simp [HC],
  },
  -- 3 ∉ C ∧ ∃ c, c ≥ 4 ∧ c ∈ C 
  have HL := cases_for_L1 G.loops G.loops_are_long_and_even,
  cases HL,
  { right,left,split,swap,exact HL,
    symmetry,rw filter_eq_self,
    intros c Hc,
    have H := G.chains_are_long c Hc,
    cases eq_or_lt_of_le H with H2 H2,
      exfalso,apply HC.left,rwa ←H2 at Hc,
      exact H2,
  },
    cases HL,
    { right,right,left,
      split,symmetry,rw filter_eq_self,
        intros c Hc,    
        have H := G.chains_are_long c Hc,
        cases eq_or_lt_of_le H with H2 H2,
        exfalso,apply HC.left,rwa ←H2 at Hc,
        exact H2,
      split,swap,exact HL.1,
      symmetry,rw filter_eq_self,
      intros l Hl,
      have H := G.loops_are_long_and_even l Hl,
      cases (loop468 G.loops G.loops_are_long_and_even l Hl) with H2 H2,
        exfalso,apply HL.2.1,rwa ←H2,
      cases H2 with H2 H2,
        exfalso,apply HL.2.2,rwa ←H2,
      exact H2,
    },
    right,right,right,right,left,split,
      right,exact HL,
      simp [HC.right],
end 


-----------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------theorems--------------------------------------------------------------
open multiset 
#check @strong_induction_on 
#print prefix multiset.strong_induction_on 

theorem strong_induction_eq {α : Type} {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]






lemma cv_one_chain (G : sle) (n : nat) (P : n ≥ 3) (Hc : G.chains = multiset.cons n 0) (Hl : G.loops = 0) : cv G = n :=
begin
  unfold cv tb,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero n, have Hs : G.chains = 0 ∧ G.loops = 0, by exact zero_size G h,
   cases Hs, rw ← Hc, rw Hs_left},
  unfold fcv,
  rw [Hc, Hl, multiset.card_zero, card_cons n 0, card_zero ],
  simp, show int.of_nat n = ↑n, refl,
end 

lemma cv_one_loop (G : sle) (n : nat) (Hc : G.chains = 0) (Hl : G.loops = (n :: 0)) : cv G = n :=
begin
  unfold cv tb,
  split_ifs,
  { exfalso, apply multiset.singleton_ne_zero n, rw ← Hl, dunfold size at h, have Hs : G.loops = 0, by exact and.right (zero_size G h),
   rw Hs},
  { exfalso, apply multiset.singleton_ne_zero n, rw [← Hl, h_1 ]},
  unfold fcv,
  rw [Hc, Hl, multiset.card_zero, card_cons n 0, card_zero ],
  simp, show int.of_nat n = ↑n , refl, 
end



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

-- TODO : controlled values

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






/-lemma one_comp_case (G : sle) : ((size G) = 1) → (cv G = value G) := 
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
-/


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
    rw H₃,rw Ha,
    rw cv_one_loop,
    rw H₃, 
    rw v_one_loop,
    rw Ha,
    have Hb : a ∈ G.loops, rw Ha, exact mem_cons_self a 0, have P : a ≥ 4 ∧ 2 ∣ a, by exact sle.loops_are_long_and_even G a Hb, by exact P.left, 
    
  },
  { have H₃ : G.loops = 0 := multiset.card_eq_zero.1 H₂.right,
    have H₄ : ∃ a, G.chains = a::0 := multiset.card_one_iff_singleton.1 H₂.left,
    cases H₄ with a Ha,
    unfold value,
    rw H₃,rw Ha,
    rw cv_one_chain, rw v_one_chain, 
    have Hb : a ∈ G.chains, rw Ha, exact mem_cons_self a 0, have P : a ≥ 3, by exact sle.chains_are_long G a Hb, by exact P, 
     have Hb : a ∈ G.chains, rw Ha, exact mem_cons_self a 0, have P : a ≥ 3, by exact sle.chains_are_long G a Hb, by exact P,
     rw Ha, rw v_one_chain,  have Hb : a ∈ G.chains, rw Ha, exact mem_cons_self a 0, have P : a ≥ 3, by exact sle.chains_are_long G a Hb, by exact P,
     rw H₃,
  },
end 


#eval value_aux {3,4} {4} -- 1
#eval cv_aux {3,4} {4}  -- -1



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
    exact H5, 
  },
end 




lemma pos_add_pos (a b : nat): a ≠ 0 → a + b ≠ 0 := begin intro x, assume h:  a + b = 0, induction b with t Ht, rw add_zero at h,
unfold ne at x, by exact false.elim (x h), unfold ne at x, rw add_succ at h, rw succ_eq_add_one at h, finish end 

lemma one_not_zero : 1 ≠ 0 := begin finish end 

lemma eq_neq_mult (a b c : multiset nat) : a = b → b ≠ c → a ≠ c :=
begin
intros x y, rw x, by exact y, 
end 

lemma option_min (x y : ℕ) : min (some x) (some y) = some (min x y) :=
begin
  unfold min,
  split_ifs;refl
end 

#eval int.nat_abs 2

/-lemma need (n : nat) (Hn : n ≥ 4) : 6 + (n - 1 - 8) = value_aux (3 :: 0) (n :: 0) :=
begin 
rw value_aux_eq, rw pmap_cons, rw pmap_cons, simp, rw value_aux_eq, rw value_aux_eq, simp,  
unfold N_min, simp, unfold option_N_min, simp, ring, unfold min, split_ifs, unfold dots_and_boxes.option_N_to_N,
 show 6 + (n - 9) = n - 4 + 1, rw add_comm,   sorry, show 6 + (n - 1 - 8) = dots_and_boxes.option_N_to_N (some (1 + int.nat_abs (2 + (-↑(4) - ↑(n - 4))))), 
 sorry, simp, exfalso, sorry
end-/




lemma le_of_sub_le_sub_left_iff (m n k : nat) (Hn : m ≥ n) (Hk : m ≥ k) : m - n ≤  m - k ↔ k ≤ n :=
nat.sub_le_sub_left_iff Hk


#eval value_aux {3} {4}   

lemma loop_and_three_chain_case (G : sle) (n : nat) (Hn : n ≥ 4): G.chains = cons 3 0  → (G.loops =cons n 0 ) 
→ (cv G = value G) := 
begin
 intros a b,
unfold cv, unfold value, unfold tb, unfold fcv,
split_ifs, 
exfalso, dunfold size at h, rw b at h, simp at h, by exact false.elim ((pos_add_pos 1 (card (G.chains)) one_not_zero h )), 
exfalso, rw [← card_eq_zero] at h_1, finish,
exfalso, have p :  cons 3 0 ≠ 0,  exact cons_ne_zero,  exact false.elim ((eq_neq_mult G.chains (cons 3 0) 0 a p) h_2),
rw b, rw [ a, card_cons 3 0, card_zero, card_cons n 0, card_zero] , 
simp, show int.of_nat n - 3 = ↑(value_aux (3 :: 0) (n :: 0)),rw value_aux_eq, rw pmap_cons, rw pmap_cons, simp, rw value_aux_eq,
rw value_aux_eq, simp, unfold N_min, simp, unfold option_N_min, simp, ring, unfold min, split_ifs, unfold dots_and_boxes.option_N_to_N,
show int.of_nat n - 3 = ↑(n - 4 + 4 - 3 - 1 + 1),  rw [ nat.sub_add_cancel], rw nat.sub_add_cancel, have h3 : n ≥ 3 := le_trans (dec_trivial) Hn,
show int.of_nat n - 3 = int.of_nat (n - 3), rw int.of_nat_sub h3, refl,  exact Hn, rw [ nat.sub_add_cancel], 
show 1 ≤ n - 3, rw nat.le_sub_left_iff_add_le, ring, exact Hn, exact le_trans (dec_trivial) Hn,  exact Hn, 
exfalso, have X : n - 3 ≤ n - 1, rw le_of_sub_le_sub_left_iff n 3 1, exact dec_trivial, exact ge_trans Hn (dec_trivial), exact ge_trans Hn (dec_trivial),
have H5 : some (n - 4 + int.nat_abs (4 + (-1 - ↑(int.nat_abs 2)))) ≤ some (1 + int.nat_abs (2 + (-↑(int.nat_abs 4) - ↑(n - 4)))),
show (n - 4 + 4 - 3 - 1 + 1) ≤ (1 + int.nat_abs (2 + (-↑4 - ↑(n - 4)))), rw nat.sub_add_cancel, rw nat.sub_add_cancel,
--------------------------------------------------------------
let m := n - 4,
  have H1 : m + 4 = n,
    by simp [m, nat.add_sub_cancel' Hn],
  have H2 : 4 - 3 = 1,
    from dec_trivial,
  have H3 : 4 - 4 = 0,
    from dec_trivial,
  rw [← H1, nat.add_sub_assoc, nat.add_sub_assoc, H2, H3, ← add_sub_assoc],
  rw [← int.nat_abs_neg], simp [bit0, -add_comm],
  rw [int.coe_nat_add_one_out, add_comm (1 : ℤ), int.coe_nat_add_one_out],
  rw [int.nat_abs_of_nat, add_comm 1],
  constructor, constructor, constructor,
  from dec_trivial, from dec_trivial,
----------------------------------------------------------------------------
exact Hn,  rw nat.sub_add_cancel, show 1 ≤ n - 3, rw nat.le_sub_right_iff_add_le, show 4 ≤ n, exact Hn, 
exact le_trans (dec_trivial) Hn, exact Hn, exact false.elim (h_5 H5),
 exfalso, have I : some (1 + int.nat_abs (2 + (-↑(int.nat_abs 4) - ↑(n - 4)))) ≤ none, simp, exact false.elim (h_4 I),
 exfalso, rw a at h_3, have P : 3 ∉ (0 : multiset nat), exact not_mem_zero 3, have nh_3 : erase_dup (3 :: 0) = 3 :: 0,
 rw erase_dup_cons_of_not_mem P, rw erase_dup_zero, exact false.elim (h_3 nh_3),
end


#check @nat.le_sub_right_of_add_le 

theorem one_point_threex (G : sle) : (value G ≥ 3 ) ↔ ((cv G ≥ 3) ∨ (((count 3 G.chains = 0 ∧ squnum G = 2 % 4 )
 ∨ (count 3 G.chains = 1 ∧ squnum G = 3 % 5)) ∧ (((cv G + 4*(count 4 G.loops) < 2) ∧ (count 4 G.loops = 0 % 2 )) 
 ∨ ((cv G + 4*( count 4 G.loops) > 2) ∧ ((count 4 G.loops = 3 % 8) ∨ (count 4 G.loops = 4 % 8) ∨ 
 (count 4 G.loops = 5 % 8) ) ) ))) := 
 begin
 split, 
 intro x, 
 sorry,sorry,
 end


lemma two_point_two_1 (G : sle) (a : nat) : (card (G.chains) ≥ 2) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G:=
begin
intros y H t, 
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl, exfalso, rw h.left at y, simp at y,  exact false.elim (Q y),
exfalso, rw h.left at y, simp at y, exact false.elim (Q y),
exfalso, rw h.left at y, simp at y, exact false.elim (Q y), 
exfalso, rw h.left at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.chains = 0, exact (zero_size G h_2).left, rw e at t, finish,
refl,
exfalso, exact false.elim (h_1 H.right), 
refl, 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
refl,
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
exfalso, exact false.elim (h_1 H.right), 
refl, 
exact t, 
end


lemma two_point_two_2 (G : sle) (a : nat) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G:=
begin
intros y z H Ha, dunfold size at y,
 rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
have B : size G = 0, dunfold size, rw h_2, rw h.left, simp, 
exfalso, exact false.elim (h_1 B),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Ha , finish,
exfalso, rw h_3 at Ha, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
have P : filter (λ (x : ℕ), x ≥ 4) (G.chains) = G.chains, exact (H.left).symm, 
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0, rw ← h_5 at d, rw mem_erase_dup at d, 
rw filter_eq_self at P, have H5 := P 3 d, revert H5, exact dec_trivial,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso,have P : filter (λ (x : ℕ), x ≥ 4) (G.chains) = G.chains, exact (H.left).symm, 
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0, rw ← h_3 at d, rw mem_erase_dup at d, 
rw filter_eq_self at P, have H5 := P 3 d, revert H5, exact dec_trivial,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Ha,
end

lemma two_point_two_3 (G : sle) (a : nat) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G:=
begin
intros y z H Ha, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
have B : size G = 0, dunfold size, rw h_2, rw h.left, simp, 
exfalso, exact false.elim (h_1 B),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw H.left at h_1, finish, 
exfalso, rw [H.left, h_3] at y, simp at y, exact false.elim (Q y),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, have p : card G.loops = 1, rw h_2, simp, exact false.elim (z (and.intro H.left p)),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw [H.left, h_5] at y, simp at y, exact false.elim (Q y),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Ha,
end




lemma two_point_two_4_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have m : G.chains = 0, exact (zero_size G h_2).left, rw [m, h_1] at y, finish, 
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).right), 
refl, 
exfalso, rw h_2 at H, have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exfalso, rw h_2 at H, have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exfalso,  exact false.elim (h_1 (zero_size G h_4).right),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso,cases h_3,  rw h_3 at H, simp at H, cases H, cases H_h, cases H_h_right, rw H_h_right at H_h_left,
 have l : ¬ 3 ≥ 4, exact dec_trivial, finish,    
 rw H_h_right.right at H_h_left,
 have l : ¬ 3 ≥ 4, exact dec_trivial, finish, exact false.elim (h_6 h_3),     
exfalso,  exact false.elim (h_1 (zero_size G h_4).right),
exfalso, rw h_5 at H, finish, 
exfalso, 
cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_6 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exact Hl,
end


lemma two_point_two_4_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw h_1 at H, finish,
exfalso, rw h_1 at H, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_5 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
refl,
refl,
exact Hl,
end

lemma two_point_two_4_3 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(∃ x ≥ 4, x ∈ G.chains) → 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs, 
refl,
exfalso, rw h_2 at Hl, finish,
exfalso, rw h_3 at H, finish,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),  
exfalso, exact false.elim (h_3 h.left),
exfalso, rw h_1 at H, finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_3).left),
refl,
exfalso, cases H with a Ha, cases Ha with p q,  rw ← mem_erase_dup at q, rw h_5 at q, rw mem_cons at q, 
cases q, rw q at p,  have l : ¬ 3 ≥ 4, exact dec_trivial, finish, 
exact false.elim ((not_mem_zero a) q ),
refl,
exfalso,  exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, exact false.elim (h_1 (zero_size G h_4).left),
exfalso, rw h_5 at Hl, finish,
refl,
exact Hl,
end



lemma two_point_two_5 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
→ 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G:=
begin
intros y z H d, dunfold size at y,
rw tb_rem_chain, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.chains = 0, exact (zero_size G h_2).left, rw e at d, finish,
refl,
exfalso, have e : G.chains = 0, exact (zero_size G h_3).left, rw e at d, finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim (Q H),
exfalso, exact false.elim (h_5 H.right),
exfalso, exact false.elim (h_1 (zero_size G h_4).right), 
exfalso, rw h_5 at d, finish,
refl,
exfalso, exact false.elim (h_6 H.right),
exfalso, exact false.elim (h_1 (zero_size G h_4).right), 
exfalso, rw h_5 at d, finish,
exfalso, rw h_6 at h_3, finish, 
refl,
exact d,
end

lemma two_point_two_6_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
→ 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw h_2 at Hl, finish,
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, exact false.elim ( h_3 H.right),
exfalso, exact false.elim ( h_3 H.right),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
refl,
exact Hl,
end




lemma two_point_two_6_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
→ 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exfalso, exact false.elim ( h_1 H.right),
exfalso, exact false.elim ( h_1 H.right),
refl,
exact Hl,
end


lemma two_point_two_7_1 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2)
→ 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, have e : G.loops = 0, exact (zero_size G h_2).right, rw e at Hl , finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_3).right, rw e at Hl , finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim ( Q H.right),
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
refl,
refl,
exact Hl,
end




lemma two_point_two_7_2 (G : sle) : (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2)
→ 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G:=
begin
intros y z H Hl, dunfold size at y,
rw tb_rem_loop, unfold tb, have Q : ¬ 1 ≥ 2, exact dec_trivial, split_ifs,
refl, 
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw [h.left, h.right] at y, simp at y, exact false.elim (Q y),
exfalso, rw h_1 at H, finish,
exfalso, rw h_3 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_3).right, rw e at Hl , finish,
refl,
exfalso, rw h_2 at H, simp at H, exact false.elim ( Q H.right),
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
exfalso, rw h_5 at Hl, finish,
refl,
exfalso, have e : G.loops = 0, exact (zero_size G h_4).right, rw e at Hl , finish,
refl,
refl,
exact Hl,
end

lemma sum_rem_c (a : multiset nat) (c : nat): c ∈ a → sum (erase a c) = sum a - c :=
begin 
intro Hc, have h : ∃ t, a = c :: t, exact exists_cons_of_mem Hc, cases h with t Ht, rw Ht,
 simp, rw add_comm, rw nat.add_sub_cancel,
end

lemma card_rem_c (a : multiset nat) (c : nat): c ∈ a → card (erase a c) = card a - 1 :=
begin 
intro Hc, have h : ∃ t, a = c :: t, exact exists_cons_of_mem Hc, cases h with t Ht, rw Ht,
 simp, rw add_comm, rw nat.add_sub_cancel,
end


lemma multiset_sum_ge_c (a : multiset nat) (c : nat) : c ∈ a → sum a ≥ c := 
begin
intro x, have h : ∃ t, a = c :: t, exact exists_cons_of_mem x, cases h with t Ht, rw Ht,
 simp, induction  (sum t) with n Hn, finish, rw succ_eq_add_one, rw ← add_assoc,  
 show c ≤ c + n + 1, rw le_add_one_iff , left, exact Hn, 
end


lemma multiset_card_ge_1 (a : multiset nat) (c : nat) : c ∈ a → card a ≥ 1 := 
begin
intro x, have h : ∃ t, a = c :: t, exact exists_cons_of_mem x, cases h with t Ht, rw Ht,
 simp, induction  (card t) with n Hn, finish, rw succ_eq_add_one, rw ← add_assoc,  
 show 1 ≤ 1 + n + 1, rw le_add_one_iff , left, exact Hn, 
end


lemma rem_three_chain_cv (G : sle) : 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G → cv (rem_chain_from_sle G 3) = cv G + 1 :=
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_chain, unfold fcv, rw sum_rem_c G.chains 3 x, rw card_rem_c G.chains 3 x, 
rw ← add_assoc, 
let n := sum (G.chains) - 3, let m := (card (G.chains) - 1),
have Hn : sum (G.chains) ≥ 3, exact multiset_sum_ge_c G.chains 3 x, 
have Hn1 : sum (G.chains) = n + 3, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.chains) ≥ 1, exact multiset_card_ge_1 G.chains 3 x, 
have Hm1 : card (G.chains) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib,
simp, show int.of_nat n + (int.of_nat (sum (G.loops)) + (↑(tb G) + (-(↑m * 4) + -(↑(card (G.loops)) * 8)))) =
    1 + (int.of_nat (n) + 3 + (int.of_nat (sum (G.loops)) + (↑(tb G) + (-4 + (-(↑m * 4) + -(↑(card (G.loops)) * 8)))))),  
rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, rw add_comm 1 (int.of_nat n), 
show int.of_nat n + int.of_nat (sum (G.loops)) + ↑(tb G) + -(↑m * 4) + -(↑(card (G.loops)) * 8) =
    int.of_nat n + 4 + int.of_nat (sum (G.loops)) + ↑(tb G) + -4 + -(↑m * 4) + -(↑(card (G.loops)) * 8), simp, 
 exact x,
end


lemma rem_three_chain_to_cb_ge_3 (G : sle) : 2 ≤ cv G → 3 ∈ G.chains → tb (rem_chain_from_sle G 3) = tb G → cv (rem_chain_from_sle G 3) ≥ 3:=
begin 
intros H x y , rw [rem_three_chain_cv G x y], show 3 ≤ (cv G) + 1, rw le_iff_eq_or_lt at H, cases H, rw ← H, simp, 
rw le_iff_eq_or_lt, right, rw int.lt_add_one_iff, rw ← int.add_one_le_iff at H, finish,
end


lemma rem_four_loop_cv (G : sle) : 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G → cv (rem_loop_from_sle G 4) = cv G + 4 := 
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_loop, unfold fcv, rw sum_rem_c G.loops 4 x, rw card_rem_c G.loops 4 x, 
rw ← add_assoc, 
let n := sum (G.loops) - 4, let m := (card (G.loops) - 1),
have Hn : sum (G.loops) ≥ 4, exact multiset_sum_ge_c G.loops 4 x, 
have Hn1 : sum (G.loops) = n + 4, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.loops) ≥ 1, exact multiset_card_ge_1 G.loops 4 x, 
have Hm1 : card (G.loops) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib, simp, 
show int.of_nat n + (int.of_nat (sum (G.chains)) + (↑(tb G) + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))) =
    4 + (int.of_nat (sum (G.chains)) + (↑(tb G) + (int.of_nat n + 4 + (-8 + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))))),
 rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, simp, 
  rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
show int.of_nat (sum (G.chains)) + ↑(tb G) + -(↑m * 8) + -(↑(card (G.chains)) * 4) =
    8 + int.of_nat (sum (G.chains)) + ↑(tb G) + -8 + -(↑m * 8) + -(↑(card (G.chains)) * 4),
    simp, exact x,
end


lemma rem_four_loop_to_cb_ge_4 (G : sle) : 2 ≤ cv G → 4 ∈ G.loops → tb (rem_loop_from_sle G 4) = tb G → cv (rem_loop_from_sle G 4) ≥ 4:=
begin 
intros H x y , rw [rem_four_loop_cv G x y], show 4 ≤ (cv G) + 4, rw le_iff_eq_or_lt at H, cases H, rw ← H, simp, 
rw le_iff_eq_or_lt, right,rw lt_add_iff_pos_left, exact lt_trans (dec_trivial) H, 
end





lemma rem_six_loop_cv (G : sle) : 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G → cv (rem_loop_from_sle G 6) = cv G + 2 := 
begin
intros x y, rw add_comm, unfold cv, rw y, rw fcv_rem_loop, unfold fcv, rw sum_rem_c G.loops 6 x, rw card_rem_c G.loops 6 x, 
rw ← add_assoc, 
let n := sum (G.loops) - 6, let m := (card (G.loops) - 1),
have Hn : sum (G.loops) ≥ 6, exact multiset_sum_ge_c G.loops 6 x, 
have Hn1 : sum (G.loops) = n + 6, by simp [n, nat.add_sub_cancel' Hn],
have Hm : card (G.loops) ≥ 1, exact multiset_card_ge_1 G.loops 6 x, 
have Hm1 : card (G.loops) = m + 1, by simp [m, nat.add_sub_cancel' Hm],
rw [Hn1, Hm1, nat.add_sub_cancel, nat.add_sub_cancel], simp, rw right_distrib, simp, 
show int.of_nat n + (int.of_nat (sum (G.chains)) + (↑(tb G) + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))) =
    2 + (int.of_nat (sum (G.chains)) + (↑(tb G) + (int.of_nat n + 6 + (-8 + (-(↑m * 8) + -(↑(card (G.chains)) * 4)))))),
 rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
rw ← add_assoc, simp, 
  rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, rw ← add_assoc, 
show int.of_nat (sum (G.chains)) + ↑(tb G) + -(↑m * 8) + -(↑(card (G.chains)) * 4) =
    8 + int.of_nat (sum (G.chains)) + ↑(tb G) + -8 + -(↑m * 8) + -(↑(card (G.chains)) * 4),
    simp, exact x,
end

#check add_right_cancel


lemma rem_six_loop_to_cb_ge_4 (G : sle) : 2 ≤ cv G → 6 ∈ G.loops → tb (rem_loop_from_sle G 6) = tb G → cv (rem_loop_from_sle G 6) ≥ 4:=
begin 
intros H x y , rw [rem_six_loop_cv G x y], show 4 ≤ (cv G) + 2, rw le_iff_eq_or_lt at H, cases H, rw ← H, exact dec_trivial, 
rw le_iff_eq_or_lt, right, 
show 2 + 2 < cv G + 2, apply add_lt_add_right, exact H, 
end

lemma int_sub_le (a b : ℤ ) : b ≥ 0 →  a - b ≤ a :=
begin
intro x, induction b with t n, finish, exfalso, 
have h : ¬  -[1+ n] ≥ 0, exact dec_trivial,   
exact false.elim (h x),
end

lemma int_le_add (a b : ℤ ) : b ≥ 0 →  a ≤ b + a :=
begin
intro x, induction b with t n, finish, exfalso, 
have h : ¬  -[1+ n] ≥ 0, exact dec_trivial,   
exact false.elim (h x),
end

lemma rem_chain_no_loops_fcv_pos (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → fcv (rem_chain_from_sle G a) ≥ 0 :=
begin 
intros x y, rw fcv_rem_chain G a y, rw x.right, simp, rw card_rem_c G.chains a y, rw sum_rem_c G.chains a y, 
rw x.left, 
show (0: ℤ)  +
      (↑  (sum (filter (λ (x : ℕ), x ≥ 4) (G.chains)) - a) +
         -(↑(card (filter (λ (x : ℕ), x ≥ 4) (G.chains)) - 1) * 4)) ≥
    0,  rw zero_add, sorry
end

lemma cv_rem_chain_no_loops_ge_tb (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → cv (rem_chain_from_sle G a) ≥ tb (rem_chain_from_sle G a) :=
begin
intros x y, unfold cv, show  ↑(tb (rem_chain_from_sle G a)) ≤ fcv (rem_chain_from_sle G a) + ↑(tb (rem_chain_from_sle G a)), 
have h : fcv (rem_chain_from_sle G a) ≥ 0, exact (rem_chain_no_loops_fcv_pos G a x y),
exact int_le_add (↑(tb (rem_chain_from_sle G a))) (fcv (rem_chain_from_sle G a)) h, 
end

lemma tb_ge_2_for_1r (G : sle) (a : nat) : (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G  → ↑(tb (rem_chain_from_sle G a)) ≥ 2 :=
begin 
intros x y z, rw z, unfold tb, rw x.right, simp, split_ifs, 
exfalso, have e : G.chains = 0, exact (zero_size G h).left, rw e at y, finish,
exact dec_trivial,
end


--set_option pp.all true
lemma two_point_two_1r (G : sle) (a : nat) : (cv G ≥ 2) → ( ( 2 : ℤ ) ≤ card (G.chains)) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) → a ∈ G.chains → tb (rem_chain_from_sle G a) = tb G → cv (rem_chain_from_sle G a) ≥ 2:=
begin
intros x y H Ha P, sorry,
--exact le_trans  (tb_ge_2_for_1r G a H Ha P : (2 : ℤ ) ≤ _ ) (cv_rem_chain_no_loops_ge_tb G a H Ha),
end


lemma two_point_two_2r (G : sle) (a : nat) : (cv G ≥ 2) → (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 )  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G → cv (rem_loop_from_sle G a) ≥ 4:=
begin
intros x y z H Ha P,
unfold cv, rw tb_rem_loop, rw fcv_rem_loop, dunfold size at y, split_ifs,
exfalso,  rw [h.left, h.right] at y, simp at y, have Q : ¬ 1 ≥ 2, exact dec_trivial, exact false.elim (Q y),
rw h_1, simp, sorry,
rw h_2, simp, sorry,
exfalso, have P : filter (λ (x : ℕ), x ≥ 4) (G.chains) = G.chains, exact (H.left).symm, 
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0, rw ← h_3 at d, rw mem_erase_dup at d, 
rw filter_eq_self at P, sorry,
sorry,
exact Ha,
exact Ha,
end

lemma two_point_two_3r (G : sle) (a : nat) : (cv G ≥ 2) → (size G ≥ 2)  → ¬ ((G.chains = (3::0)) ∧ (card (G.loops) = 1)) → 
(G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops)  
→ a ∈ G.loops → tb (rem_loop_from_sle G a) = tb G → cv (rem_loop_from_sle G a) ≥ 4:=
begin
intros x y z H Ha P,
unfold cv, rw tb_rem_loop, rw fcv_rem_loop, dunfold size at y, split_ifs,
exfalso, have p : card G.loops = 1, rw h.right , simp, exact false.elim (z (and.intro H.left p)),
sorry,
exfalso, have p : card G.loops = 1, rw h_2 , simp, exact false.elim (z (and.intro H.left p)),
rw H.left, sorry,
sorry,
exact Ha,
exact Ha,
end









theorem two_point_two_ad (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3::0)) 
∧ (card (G.loops) = 1)) → (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))) :=
begin
intros x y z, have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, exfalso, exact false.elim (z H),
cases H, left, dunfold size at y, rw H.right at y, simp at y, have P : 0 < card G.chains, have K : 2 ≤ card (G.chains), exact y,
rw le_iff_eq_or_lt at K, cases K, rw ← K, exact dec_trivial, exact lt_trans (dec_trivial) K, rw card_pos_iff_exists_mem at P, cases P with a Ha,
have T : tb (rem_chain_from_sle G a) = tb G , 
exact two_point_two_1 G a y H Ha,----------------------------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T, sorry, ----------------------oooooooooooo
cases H,  right, have L : G.loops ≠ 0, finish, 
have LL : ∃ (a : ℕ), a ∈ G.loops, exact exists_mem_of_ne_zero L, cases LL with a Ha, 
have T : tb (rem_loop_from_sle G a) = tb G ,  
exact two_point_two_2 G a y z H Ha,--------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T, sorry,--------oooooo
cases H,  right, 
have LL : ∃ (a : ℕ), a ∈ G.loops, have n :  G.loops ≠ 0, simp, intro m, dunfold size at y, rw [m, H.left] at y, 
have Q : ¬ 1 ≥ 2, exact dec_trivial, finish, exact exists_mem_of_ne_zero n , cases LL with a Ha, 
have T : tb (rem_loop_from_sle G a) = tb G,  
exact two_point_two_3 G a y z H Ha,------------------
fapply exists.intro, exact a, fapply exists.intro, exact Ha, split, exact T, sorry,-------oooooooooooooo
cases H, have Hl: 3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops ,  exact H.left,
cases Hl, left, 
have T : tb (rem_chain_from_sle G 3) = tb G ,
exact two_point_two_4_1 G y z H.right Hl,------------------------
fapply exists.intro, exact 3, fapply exists.intro, exact Hl, 
split, exact T, sorry,-------------ooooooooooooooooo
cases Hl, right, 
have T : tb (rem_loop_from_sle G 4) = tb G , 
  exact two_point_two_4_2 G y z H.right Hl,-----------------
fapply exists.intro, exact 4, fapply exists.intro, exact Hl,split, exact T, sorry,----------------oooooooooooooooooooooo
right, 
have T : tb (rem_loop_from_sle G 6) = tb G , 
 exact two_point_two_4_3 G y z H.right Hl,--------------------
fapply exists.intro, exact 6, fapply exists.intro, exact Hl,split, exact T, sorry,-------ooooooooooooooooooooo
cases H, left,
have d : 3 ∈ multiset.cons 3 0, exact mem_cons_self 3 0,-- rw ← h_3 at d, rw mem_erase_dup at d, 
rw ← H.right at d, rw mem_erase_dup at d,  
have T : tb (rem_chain_from_sle G 3) = tb G ,
  exact two_point_two_5 G y z H d,---------------
fapply exists.intro, exact 3, fapply exists.intro, exact d,split, exact T, sorry,-------ooooooooooooooooooooooooooooo
cases H, right, have Hl: 4 ∈ G.loops ∨ 6 ∈ G.loops , exact H.left,
cases Hl, have T : tb (rem_loop_from_sle G 4) = tb G , 
 exact two_point_two_6_1 G y z H Hl,--------------------
fapply exists.intro, exact 4, fapply exists.intro, exact Hl, split, exact T, sorry,-------------------ooooooooooooooooooooo
have T : tb (rem_loop_from_sle G 6) = tb G, 
 exact two_point_two_6_2 G y z H Hl,--------------------
fapply exists.intro, exact 6, fapply exists.intro, exact Hl, split, exact T, sorry,-----------oooooooooooooooooooooooooooooooooo
dunfold size at y, right, have Hl: 4 ∈ G.loops ∨ 6 ∈ G.loops , exact H.left,
cases Hl, have T : tb (rem_loop_from_sle G 4) = tb G, 
exact two_point_two_7_1 G y z H Hl,
fapply exists.intro, exact 4, fapply exists.intro, exact Hl, split, exact T, sorry,
have T : tb (rem_loop_from_sle G 6) = tb G , 
 exact two_point_two_7_2 G y z H Hl,
fapply exists.intro, exact 6, fapply exists.intro, exact Hl, split, exact T, sorry
end

theorem two_point_two (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1)) → (int.of_nat (value G) = cv G):=
begin
intros x y z, 
have H : (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))), exact two_point_two_ad G x y z,
cases H, cases H with c Hc, cases Hc with t Ht, sorry, sorry,
end

/-
lemma three_point_one (G : sle) : (G ≠ empty_game) → (G.chains = filter (λ x, x ≥ 4) G.chains) → (G.loops = filter (λ x, x ≥ 6) G.loops) →  
(value G ≥ 2) := 
begin
intros x y z, unfold value, rw value_aux_eq, 
show  N_min
      (pmap (λ (a : ℕ) (h : a ∈ G.chains), v_of_G_with_chain G a)
           (G.chains)
           _ +
         pmap
           (λ (a : ℕ) (h : a ∈ G.loops), v_of_G_with_loop G a)
           (G.loops)
           _) ≥
    2, 
    rw y
    
  sorry,
end
-/



theorem for_two_point_three (G : sle) : cv G ≥ 2 → size G ≥ 2 → (G.chains = (3 :: 0)) 
∧ (multiset.card(G.loops) = 1) → int.of_nat (value G) = cv G :=
begin
intros x y z, have H : ∃ x, G.loops = x :: 0, exact  multiset.card_one_iff_singleton.1 z.right, cases H with a Pa,
show ↑ (value G) = cv G,
rw [ ← loop_and_three_chain_case G a],
have n : a ∈ a :: 0, exact mem_cons_self a 0, rw ← Pa at n, exact (G.loops_are_long_and_even a n).left,
exact z.left,
exact Pa, 
end






theorem two_point_three (G : sle) : cv G ≥ 2 → int.of_nat (value G) = cv G := sorry
--by theorems from before


theorem one_point_three (G : simple_loony_endgame) : (value_G G ≥ 3 ) ↔ ((cv_G G ≥ 3) ∨  (((G.three_chains = 0 ∧ squnum_G G = 2 % 4 )
 ∨ (G.three_chains = 1 ∧ squnum_G G = 3 % 5)) ∧ (((cv_G G + 4*G.four_loops < 2) ∧ (G.four_loops = 0 % 2 )) 
 ∨ ((cv_G G + 4*G.four_loops > 2) ∧ ((G.four_loops = 3 % 8) ∨ (G.four_loops = 4 % 8) ∨ (G.four_loops = 5 % 8) ) ) ))) :=
begin
 split, 
 intro x, 
 induction G.three_chains with t Ht, induction G.four_loops with f Hf, simp, 
 sorry, simp, sorry, sorry, sorry
 end




theorem one_point_three_sle (G : sle) : (value G ≥ 3 ) ↔ ((cv G ≥ 3) ∨  (((3 ∉ G.chains ∧ squnum G = 2 % 4 )
 ∨ (count 3 G.chains = 1 ∧ squnum G = 3 % 5)) ∧ (((cv G + 4*(count 4 G.loops) < 2) ∧ (count 4 G.loops = 0 % 2 )) 
 ∨ ((cv G + 4*count 4 G.loops > 2) ∧ ((count 4 G.loops = 3 % 8) ∨ (count 4 G.loops = 4 % 8) ∨ (count 4 G.loops = 5 % 8) ) ) ))) :=
begin
 split, 
 intro x, 
 have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, sorry,
 sorry,
  simp, sorry, 
 end




/-
theorem two_point_two (G : simple_loony_endgame) : (cv_G G ≥ 2) → (size_G G ≥ 2) → ¬ ((G.three_chains = 1) 
∧ (multiset.card(all_loops G) = 1)) → (value G = cv_G G):= sorry-/


theorem three_point_two_1 (G: sle) : ((size G) > 0) → (cv G < 2) → (value G ≤ 4) := sorry


lemma count_imp_card {m : multiset nat} {a b : nat} : count a m ≥ b → card m ≥ b :=
begin
intro x, 
sorry
end

--lemma three_point_two (G: simple_loony_endgame) : ((size_G G) > 0) → (cv_G G < 2) → (value_G G ≤ 4) ∧ ((G.three_chains > 0) ∨
--(G.four_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops ≥ 2 ∧ (size_G G) > 2)) := sorry

theorem three_point_two (G: sle) : ((size G) > 0) → (cv G < 2) → (value G ≤ 4) → ((count 3 G.chains > 0 ∧ (size G) > 1) ∨
(count 4 G.loops > 0 ∧ (size G) > 1) ∨ (count 6 G.loops > 1 ∧ (size G) > 2)) := 
begin
intros x y z, dunfold size at x,  
have H : (G.chains = multiset.cons 3 0 ∧ multiset.card G.loops = 1)
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = 0 ) 
∨ (G.chains = multiset.filter (λ x, x ≥ 4) G.chains ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops ∧ G.loops ≠ 0 ) 
∨ (G.chains = multiset.cons 3 0 ∧ G.loops = multiset.filter (λ x, x ≥ 8) G.loops) 
∨ ((3 ∈ G.chains ∨ 4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ ∃ x ≥ 4, x ∈ G.chains)
∨ (multiset.count 3 G.chains ≥ 2 ∧ multiset.erase_dup G.chains = multiset.cons 3 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = 0)
∨ ((4 ∈ G.loops ∨ 6 ∈ G.loops) ∧ G.chains = multiset.cons 3 0 ∧ multiset.card G.loops ≥ 2), exact exhaustive_cases G, 
cases H, left, rw H.left, simp, split, exact dec_trivial, dunfold size, rw H.left, rw H.right, exact dec_trivial,
cases H, exfalso, unfold cv at y, unfold fcv at y, rw H.right at y, rw H.left at y, simp at y, sorry,
cases H, exfalso,  sorry,
cases H, left, rw H.left, simp, split, exact dec_trivial, dunfold size, rw H.left, sorry,
cases H, cases H.left, left, have P : ∃ t, G.chains = 3 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 3 t), 
sorry,
cases h, right, left, have P : ∃ t, G.loops = 4 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 4 t), 
sorry,
right, right,  have P : ∃ t, G.loops = 6 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, sorry, sorry, 
cases H, left, split, sorry,
have P : card (G.chains) ≥ 2, exact count_imp_card H.left, dunfold size, sorry,
cases H, cases H.left, right, left, have P : ∃ t, G.loops = 4 :: t, exact exists_cons_of_mem h, cases P with t ht, 
split, rw ht, simp, exact zero_lt_succ (count 4 t), sorry, sorry, sorry,
end

lemma three_point_two_f (G: sle) : ((size G) > 0) → (cv G < 2) → if mem 3 G.chains then value G ≤ 3 ∧ value (rem_chain_from_sle G 3) ≤ 4 
else if mem 4 G.loops then value (rem_loop_from_sle G 4) ≤ 5 else  value (rem_loop_from_sle G 6) ≤ 4 := 
begin
intros x y, split_ifs, split, have z : (value G ≤ 4),
exact (three_point_two_1 G x y),  

 sorry, sorry, sorry, sorry

end

theorem three_point_three (G : sle) : G_is_even G → 
if size G = 0 then value G = 0
else if cv G > 2 then int.of_nat (value G) = cv G
else if cv G = 0 ∧ 3 ∈ G.chains ∧ 4 ∈ G.loops ∧ ((∃ c ∈ G.chains, c ≥ 4) ∨ (∃ c ∈ (rem_loop_from_sle G 4).loops, c ≥ 4)) then value G = 0
else if cv G < 2 ∧ 4 ∣ (cv G) ∧ 3 ∉ G.chains ∧ cv G + 4 * (count 4 G.loops) < 2 then value G = (if 2 ∣ count 4 G.loops then 4 else 0)
else if cv G < 2 ∧ 4 ∣ (cv G) ∧ 3 ∉ G.chains ∧ cv G + 4 * (count 4 G.loops) > 2 then value G = (if cv G % 8 = 0 then 0 else 4)
else value G = 2 := 
begin
intro x, split_ifs, rw ← empty_game_iff_size_zero at h,  rw h, unfold empty_game_sle, 
show value
      {chains := 0,
       chains_are_long := empty_game_sle._proof_1,
       loops := 0,
       loops_are_long_and_even := empty_game_sle._proof_2} =
    0,
unfold value, simp, rw lt_iff_le_and_ne at h_1, exact two_point_three G h_1.left,
unfold value, rw value_aux_eq, 
sorry,
sorry,
sorry,
sorry,
sorry,
sorry,
end

--nat.mod_two_eq_zero_or_one


import data.multiset
import order.bounded_lattice
import data.finset
import extended_N_le tactic.ring
import init.algebra.functions

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

def size_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G)

definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

def size (e : sle) : ℕ := multiset.card e.chains + multiset.card e.loops



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

--------------------------------need the following definition and lemma to return a sum 
--------------------------------of integers and not the ineger of a sum of nats

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



def cv_G (G : simple_loony_endgame) : int := fcv_G G + tb_G G

definition cv_aux (C L : multiset ℕ) : ℤ := fcv_aux C L + tb_aux C L

def cv (G : sle): int := fcv G + tb G

lemma cv_zero : cv empty_game_sle = 0 := dec_trivial 



def loop_move_is_optimal_G (G : simple_loony_endgame) (a: nat): Prop  :=
value_G G = a - 4 + int.nat_abs (4 - value_aux (all_chains G) ((all_loops G).erase a))

def loop_move_is_optimal (G : sle) (a: nat): Prop  :=
value G = a - 4 + int.nat_abs (4 - value_aux (G.chains) ((G.loops).erase a))

def chain_move_is_optimal_G (G : simple_loony_endgame) (a: nat): Prop  :=
value_G G = a - 2 + int.nat_abs (2 - value_aux ((all_chains G).erase a) (all_loops G))

def chain_move_is_optimal (G : sle) (a: nat): Prop  :=
value G = a - 2 + int.nat_abs (2 - value_aux ((G.chains).erase a) (G.loops))

--set_option class.instance_max_depth

/-def v_G (G : simple_loony_endgame):  simple_loony_endgame → int
| x := if h : x = empty_game then 0 else if i : x =  (game_three_succ G) then (min (v_G G - 3) (2 - 3 - (v_G G))) else 
if j : x = (game_four_succ G) then 
have size_G G < size_G x, from begin rw[j], unfold game_four_succ, unfold simple_loony_endgame.sizeof,   end,
-/



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



-----------------------------------------------------------------------------------------------------------------------------------
-------------------------------------------------------------theorems--------------------------------------------------------------
open multiset 
#check @strong_induction_on 
#print prefix multiset.strong_induction_on 

theorem strong_induction_eq {α : Type} {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]

@[simp] lemma v_empty : value_aux 0 0 = 0 := by {rw value_aux_eq, simp}


lemma zero_sum (a b : nat) : a + b = 0 → a = 0 ∧ b = 0 := begin intro x, split, induction b with t Ht,
  rw ← x, simp, exfalso, rw add_succ at x, finish, induction a with t Ht,
  rw ← x, simp, exfalso, rw succ_add at x, finish,  end 

lemma zero_size (G : sle) : size G = 0 → G.chains = 0 ∧ G.loops = 0 :=
begin
intro x, dunfold size at x, have y : card G.chains = 0 ∧ card G.loops = 0, by exact zero_sum (card G.chains) (card G.loops) x, split,
cases y, rw ← card_eq_zero,  exact y_left, cases y, rw ← card_eq_zero,  exact y_right,
end


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


lemma two_a (G : sle) (m n : nat) ( Hm : 3 ≤ m) (Hn : 3 ≤ n ):   m ≤ n → int.nat_abs ( value ( cons_chain_to_sle G m Hm) - value ( cons_chain_to_sle G n Hn )) ≤ n - m :=
begin 
intro x,  induction m with t Pt, induction n with s Ps, exfalso, have N : ¬ 3 ≤ 0, exact dec_trivial, exact false.elim (N Hn), 
exfalso, have N : ¬ 3 ≤ 0, exact dec_trivial, exact false.elim (N Hm), unfold value, sorry,
end


#eval value_aux {3} {4}   

lemma loop_and_three_chain_case (G : sle) (n : nat) (Hn : n ≥ 4) (He : 2 ∣ n) : G.chains = cons 3 0  → (G.loops =cons n 0 ) 
→ (cv G = int.of_nat (value G)) := 
begin
 intros a b,
unfold cv, unfold value, unfold tb, unfold fcv,
split_ifs, 
exfalso, dunfold size at h, rw b at h, simp at h, by exact false.elim ((pos_add_pos 1 (card (G.chains)) one_not_zero h )), 
exfalso, rw [← card_eq_zero] at h_1, finish,
exfalso, have p :  cons 3 0 ≠ 0, by exact cons_ne_zero, by exact false.elim ((eq_neq_mult G.chains (cons 3 0) 0 a p) h_2),
rw b, rw [ a, card_cons 3 0, card_zero, card_cons n 0, card_zero] , 
simp, show int.of_nat n - 3 = ↑(value_aux (3 :: 0) (n :: 0)),rw value_aux_eq, rw pmap_cons, rw pmap_cons, simp, rw value_aux_eq,
rw value_aux_eq, simp, unfold N_min, simp, unfold option_N_min, simp, ring, unfold min, split_ifs, unfold dots_and_boxes.option_N_to_N,
show int.of_nat n - 3 = ↑(n - 4 + 1), simp, ring, sorry,sorry,sorry,sorry,   /- by exact need n Hn,
exfalso, rw a at h_3,  rw [erase_dup_cons, erase_dup_zero, ndinsert_zero] at h_3, finish -/    
end

theorem one_point_threex (G : sle) : (value G ≥ 3 ) ↔ ((cv G ≥ 3) ∨ (((count 3 G.chains = 0 ∧ squnum G = 2 % 4 )
 ∨ (count 3 G.chains = 1 ∧ squnum G = 3 % 5)) ∧ (((cv G + 4*(count 4 G.loops) < 2) ∧ (count 4 G.loops = 0 % 2 )) 
 ∨ ((cv G + 4*( count 4 G.loops) > 2) ∧ ((count 4 G.loops = 3 % 8) ∨ (count 4 G.loops = 4 % 8) ∨ 
 (count 4 G.loops = 5 % 8) ) ) ))) := 
 begin
 split, 
 intro x, 
 sorry,sorry,
 end

theorem two_point_one_ad (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((count 3 G.chains = 1) 
∧ (card (G.loops) = 1)) → (( ∃ C ∈ (G.chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))) :=
begin
intros x y z,  sorry 
end

theorem two_point_two (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((count 3 G.chains = 1) 
∧ (multiset.card(G.loops) = 1)) → (int.of_nat (value G) = cv G):=
begin
intros x y z, unfold value, unfold cv, unfold fcv tb, split_ifs, 
exfalso, rw h at y, have N : ¬  0 ≥  2, by exact dec_trivial, by exact false.elim (N y),
rw h_1, simp, rw value_aux_eq, simp, 
sorry,sorry,sorry,sorry 
end

lemma three_point_one (G : sle) : ((size G) > 0) → (count 3 G.chains = 0) → (count 4 G.loops = 0) →  
(value G ≥ 2) := 
begin
intros x y z, unfold value, sorry
end





theorem one_point_three (G : simple_loony_endgame) : (value_G G ≥ 3 ) ↔ ((cv_G G ≥ 3) ∨  (((G.three_chains = 0 ∧ squnum_G G = 2 % 4 )
 ∨ (G.three_chains = 1 ∧ squnum_G G = 3 % 5)) ∧ (((cv_G G + 4*G.four_loops < 2) ∧ (G.four_loops = 0 % 2 )) 
 ∨ ((cv_G G + 4*G.four_loops > 2) ∧ ((G.four_loops = 3 % 8) ∨ (G.four_loops = 4 % 8) ∨ (G.four_loops = 5 % 8) ) ) ))) :=
begin
 split, 
 intro x, 
 induction G.three_chains with t Ht, induction G.four_loops with f Hf, simp, 
 sorry, simp, sorry, sorry, sorry
 end
/-
theorem two_point_two (G : simple_loony_endgame) : (cv_G G ≥ 2) → (size_G G ≥ 2) → ¬ ((G.three_chains = 1) 
∧ (multiset.card(all_loops G) = 1)) → (value G = cv_G G):= sorry-/





--lemma three_point_two (G: simple_loony_endgame) : ((size_G G) > 0) → (cv_G G < 2) → (value_G G ≤ 4) ∧ ((G.three_chains > 0) ∨
--(G.four_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops ≥ 2 ∧ (size_G G) > 2)) := sorry

lemma three_point_two (G: sle) : ((size G) > 0) → (cv G < 2) → (value G ≤ 4) ∧ ((count 3 G.chains > 0) ∨
(count 4 G.loops > 0 ∧ (size G) > 1) ∨ (count 6 G.loops > 0 ∧ (size G) > 1) ∨ (count 6 G.loops ≥ 2 ∧ (size G) > 2)):= 
begin
intros x y, split, dunfold size at x, unfold cv at y, unfold value, sorry,  
sorry,
end

lemma three_point_two_f (G: sle) : ((size G) > 0) → (cv G < 2) → if mem 3 G.chains then value G ≤ 3 ∧ value (rem_chain_from_sle G 3) ≤ 4 
else if mem 4 G.loops then value (rem_loop_from_sle G 4) ≤ 5 else  value (rem_loop_from_sle G 6) ≤ 4 := 
begin
intros x y, split_ifs, split,   sorry, sorry, sorry, sorry

end



import data.multiset
import extended_N_le tactic.ring

open nat

/-- cons_to_the_n x y m adds x copies of y to the multiset m-/
def cons_to_the_n : ℕ → ℕ →  multiset nat →  multiset nat
| 0 a b  := b
| 1 a b := (multiset.cons a b) 
| (succ n) a b := multiset.cons a (cons_to_the_n n a b) 


/-- definition of a simple loony endgame (=sle) explicitly metioning 3c's, 4l's and 6'ls-/
/- from now on referred to as long def when the context is clear-/
structure simple_loony_endgame :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, 4 ≤ x)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, 8 ≤ x)
(long_loops_are_even : ∀ x ∈ long_loops, 2 ∣ x)

/-- empty game regarding long def-/
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

/--size of a simple_loony_endgame (number of components)-/
def size_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G)

/--multiset containing all chains of a simple_loony_endgame-/
def all_chains (G : simple_loony_endgame): multiset nat :=
(cons_to_the_n G.three_chains 3 G.long_chains)

/--multiset containing all loops of a simple_loony_endgame-/
def all_loops (G : simple_loony_endgame):=
(cons_to_the_n G.four_loops 4 (cons_to_the_n G.six_loops 6 G.long_loops))

-----------------------------------------------------------------------------------------

/--definition of a simple loony endgame (=sle)-/
--from now on referred to as short def when the context is clear
structure sle :=
(chains : multiset ℕ)
(chains_are_long : ∀ x ∈ chains, 3 ≤ x)
(loops : multiset ℕ)
(loops_are_long_and_even : ∀ x ∈ loops, 4 ≤ x ∧ 2 ∣ x)

/-- empty game regarding short def-/
definition empty_game_sle : sle := {chains := ∅,chains_are_long := dec_trivial, 
  loops := ∅, loops_are_long_and_even := dec_trivial}



/-- auxiliary function used to define the size of an sle -/
definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

/--size of a sle (number of components)-/
def size (e : sle) : ℕ := multiset.card e.chains + multiset.card e.loops



/-- auxiliary function used to define value -/
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
/-- auxilary lemma for value equality between sle -/
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

/--value of a simple_loony_endgame-/
definition value_G (G : simple_loony_endgame) := value_aux (all_chains G) (all_loops G)

/--value of a sle-/
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
+-- this does no
-/


/--fully controlled value of a simple_loony_endgame-/
def fcv_G (G : simple_loony_endgame): int :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + int.of_nat (multiset.sum (simple_loony_endgame.long_loops G) )
+ int.of_nat (multiset.sum (simple_loony_endgame.long_chains G)) 
- (multiset.card (simple_loony_endgame.long_chains G) + 1)*4 
- (multiset.card (simple_loony_endgame.long_loops G) + 2)*8 

/--fully controlled value of a sle-/
def fcv (G : sle):= int.of_nat (multiset.sum G.chains) + int.of_nat (multiset.sum G.loops) - (multiset.card (G.chains))*4 
- (multiset.card (G.loops))*8 



/-- auxiliary function used to define fully controlled value -/
definition fcv_aux (C L : multiset ℕ) : ℤ := ↑(multiset.sum C + multiset.sum L) 
  - 4 * multiset.card C - 8 * multiset.card L

definition fcv_KB (G : sle) : ℤ := fcv_aux G.chains G.loops


/--terminal bonus of a simple_loony_endgame-/
def tb_G (G : simple_loony_endgame)  :=
if size_G G = 0 then 0
else if multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (simple_loony_endgame.long_loops G) + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G = 0 then 4
else if simple_loony_endgame.long_chains G = multiset.zero then 6
else 4

/-- Being in a multiset and satisfying a decidable predicate is decidable -/
instance decidable_exists_multiset {α : Type*} (s : multiset α)
  (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) := quotient.rec_on s
list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

/-- Being in a multiset and being ≥ n is decidable -/
instance (C : multiset ℕ) (n : ℕ) : decidable (∃ a : ℕ, n ≤ a ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ n),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

/-- auxiliary function used to define terminal bonus -/
definition tb_aux (C L : multiset ℕ) : ℕ := if (C = 0 ∧ L = 0) then 0 else
  if L = 0 then 4 else
  if C = 0 then 8 else 
  if ∃ a : ℕ, 4 ≤ a ∧ a ∈ C then 4 else 
  6

/--terminal bonus of a sle-/
def tb (G : sle)  :=
if size G = 0 then 0
else if  G.loops = 0 then 4
else if  G.chains = 0 then 8
--else if (multiset.count 3 G.long_chains) = (multiset.card G.long_chains) then 6
else if multiset.erase_dup (G.chains) = (multiset.cons 3 0) then 6
else 4


/--controlled value of a simple_loony_endgame-/
def cv_G (G : simple_loony_endgame) : int := fcv_G G + tb_G G

/-- auxiliary function used to define controlled value -/
definition cv_aux (C L : multiset ℕ) : ℤ := fcv_aux C L + tb_aux C L

/--controlled value of a sle-/
def cv (G : sle): int := fcv G + tb G
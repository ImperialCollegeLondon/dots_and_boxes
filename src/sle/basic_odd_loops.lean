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
structure olsimple_loony_endgame :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, 4 ≤ x)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, 8 ≤ x)


/-- empty game regarding long def-/
definition olempty_game : olsimple_loony_endgame :=
{ three_chains := 0,
  four_loops := 0,
  six_loops := 0,
  long_chains := multiset.zero,
  long_chains_are_long := λ x Hx, false.elim Hx,
  long_loops := {},
  long_loops_are_long := λ x Hx, false.elim Hx,
}

/--size of a simple_loony_endgame (number of components)-/
def olsize_G (G : olsimple_loony_endgame) :=
olsimple_loony_endgame.three_chains G + olsimple_loony_endgame.four_loops G 
+ olsimple_loony_endgame.six_loops G + multiset.card (olsimple_loony_endgame.long_loops G) 
+ multiset.card (olsimple_loony_endgame.long_chains G)

/--multiset containing all chains of a simple_loony_endgame-/
def all_chains (G : olsimple_loony_endgame): multiset nat :=
(cons_to_the_n G.three_chains 3 G.long_chains)

/--multiset containing all loops of a simple_loony_endgame-/
def all_loops (G : olsimple_loony_endgame):=
(cons_to_the_n G.four_loops 4 (cons_to_the_n G.six_loops 6 G.long_loops))

-----------------------------------------------------------------------------------------

/--definition of a simple loony endgame (=sle)-/
--from now on referred to as short def when the context is clear
structure olsle :=
(chains : multiset ℕ)
(chains_are_long : ∀ x ∈ chains, 3 ≤ x)
(loops : multiset ℕ)
(loops_are_long : ∀ x ∈ loops, 4 ≤ x)

/-- empty game regarding short def-/
definition empty_game_olsle : olsle := {chains := ∅,chains_are_long := dec_trivial, 
  loops := ∅, loops_are_long := dec_trivial}



/-- auxiliary function used to define the size of an sle -/
definition size_aux (C L : multiset ℕ) := multiset.card C + multiset.card L 

/--size of a sle (number of components)-/
def olsize (e : olsle) : ℕ := multiset.card e.chains + multiset.card e.loops



/-- auxiliary function used to define value -/
def olvalue_aux : multiset ℕ → multiset ℕ → ℕ
| C L := multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C), 
        have multiset.card (C.erase a) < multiset.card C,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card (C.erase a) + multiset.card L < multiset.card C + multiset.card L, 
--          from add_lt_add_right (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
         a - 2 + int.nat_abs (2 - olvalue_aux (C.erase a) L))
        C (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L), 
        have multiset.card (L.erase a) < multiset.card L,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card C + multiset.card (multiset.erase L a) < multiset.card C + multiset.card L, 
--          from add_lt_add_left (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
         a - 4 +int.nat_abs (4 - olvalue_aux C (L.erase a)))
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
lemma olvalue_aux_eq (C L : multiset ℕ) : 
olvalue_aux C L = multiset.N_min 
  (multiset.pmap
    (λ a (h : a ∈ C), 
      a - 2 + int.nat_abs (2 - olvalue_aux (C.erase a) L))
        C (λ _,id) 
  + multiset.pmap 
    (λ a (h : a ∈ L), 
      a - 4 +int.nat_abs (4 - olvalue_aux C (L.erase a)))
        L (λ _,id)
  ) := olvalue_aux._main.equations._eqn_1 C L 

/--value of a simple_loony_endgame-/
definition olvalue_G (G : olsimple_loony_endgame) := olvalue_aux (all_chains G) (all_loops G)

/--value of a sle-/
definition olvalue (G : olsle) := olvalue_aux G.chains G.loops



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
def olfcv_G (G : olsimple_loony_endgame): int :=
olsimple_loony_endgame.three_chains G + olsimple_loony_endgame.four_loops G 
+ olsimple_loony_endgame.six_loops G + int.of_nat (multiset.sum (olsimple_loony_endgame.long_loops G) )
+ int.of_nat (multiset.sum (olsimple_loony_endgame.long_chains G)) 
- (multiset.card (olsimple_loony_endgame.long_chains G) + 1)*4 
- (multiset.card (olsimple_loony_endgame.long_loops G) + 2)*8 

/--fully controlled value of a sle-/
def olfcv (G : olsle):= int.of_nat (multiset.sum G.chains) + int.of_nat (multiset.sum G.loops) - (multiset.card (G.chains))*4 
- (multiset.card (G.loops))*8 



/-- auxiliary function used to define fully controlled value -/
definition olfcv_aux (C L : multiset ℕ) : ℤ := ↑(multiset.sum C + multiset.sum L) 
  - 4 * multiset.card C - 8 * multiset.card L

definition olfcv_KB (G : olsle) : ℤ := olfcv_aux G.chains G.loops


/--terminal bonus of a simple_loony_endgame-/
def oltb_G (G : olsimple_loony_endgame)  :=
if olsize_G G = 0 then 0
else if multiset.card (olsimple_loony_endgame.long_chains G) + olsimple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (olsimple_loony_endgame.long_loops G) + olsimple_loony_endgame.four_loops G 
+ olsimple_loony_endgame.six_loops G = 0 then 4
else if olsimple_loony_endgame.long_chains G = multiset.zero then 6
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
definition oltb_aux (C L : multiset ℕ) : ℕ := if (C = 0 ∧ L = 0) then 0 else
  if L = 0 then 4 else
  if C = 0 then 8 else 
  if ∃ a : ℕ, 4 ≤ a ∧ a ∈ C then 4 else 
  6

/--terminal bonus of a sle-/
def oltb (G : olsle)  :=
if olsize G = 0 then 0
else if  G.loops = 0 then 4
else if  G.chains = 0 then 8
--else if (multiset.count 3 G.long_chains) = (multiset.card G.long_chains) then 6
else if multiset.erase_dup (G.chains) = (multiset.cons 3 0) then 6
else 4


/--controlled value of a simple_loony_endgame-/
def olcv_G (G : olsimple_loony_endgame) : int := olfcv_G G + oltb_G G

/-- auxiliary function used to define controlled value -/
definition olcv_aux (C L : multiset ℕ) : ℤ := olfcv_aux C L + oltb_aux C L

/--controlled value of a sle-/
def olcv (G : olsle): int := olfcv G + oltb G


 
def rem_chain_from_olsle (G : olsle) (a:nat) : olsle :=
{
  chains := (multiset.erase (olsle.chains G) a),
  chains_are_long := begin intros, have H2 : (x ∈ G.chains), by exact multiset.mem_of_mem_erase H,
  clear H, have H1 : ∀ x ∈ G.chains, 3 ≤ x, by exact G.chains_are_long, finish, end,
  loops := (olsle.loops G),
  loops_are_long := G.loops_are_long
}



def rem_loop_from_olsle (G : olsle) (a:nat) : olsle :=
{
  chains := (olsle.chains G),
  chains_are_long := G.chains_are_long,
  loops := (multiset.erase (olsle.loops G) a),
  loops_are_long := begin intros, have H1 : (x ∈ G.loops),
  by exact multiset.mem_of_mem_erase H, have H2 : ∀ x ∈ G.loops, x ≥ 4,  by exact G.loops_are_long,
  have H1 : (x ∈ G.loops),
  by exact multiset.mem_of_mem_erase H, finish,  end
} 







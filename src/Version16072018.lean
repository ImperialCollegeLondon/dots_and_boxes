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

@[simp] lemma option_N_none : option_N_to_N none = 0 := rfl 

@[simp] lemma N_min_empty : multiset.N_min 0 = 0 := rfl 

@[simp] lemma N_min_singleton (a : ℕ) : multiset.N_min (a :: 0) = a :=
begin
  unfold multiset.N_min,simp,
  unfold multiset.option_N_min,simp,
  unfold min,rw if_pos,unfold option_N_to_N,
  unfold has_le.le,
end 


def cons_to_the_n : ℕ → ℕ →  multiset nat →  multiset nat
| 0 a b  := b
| 1 a b := (multiset.cons a b) 
| (succ n) a b := multiset.cons a (cons_to_the_n n a b) 

lemma lenpre (y z m : nat)(α : multiset nat) : (z ≥ y) → (∀ x ∈ α , x ≥ y) → (∀ x ∈ cons_to_the_n m z α , x ≥ y) :=
begin
intros, induction m with t Pt, unfold cons_to_the_n at H, finish, 
have Hn :  x ∈ multiset.cons z (cons_to_the_n t z α), sorry,
 rw[multiset.mem_cons] at Hn, cases Hn, rw Hn, by exact a, by exact Pt Hn,
end

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

def simple_loony_endgame_to_sle (G : simple_loony_endgame) : sle :=
{
  long_chains := (all_chains G),
  long_chains_are_long := begin intros, unfold all_chains at H, have P : 3 ≥ 3 , finish, have K : 4 ≥ 3, by exact dec_trivial,   
  have Q : ∀ x ∈ G.long_chains, x ≥ 3 , sorry, 
  have R: ∀ (x : ℕ), x ∈ cons_to_the_n (G.three_chains) 3 (G.long_chains) → x ≥ 3,
  by exact lenpre 3 3 G.three_chains (G.long_chains) P Q, finish,  end,
  long_loops := (all_loops G),
  long_loops_are_long_and_even := sorry
}

 

def rem_chain_from_sle (G : sle) (a:nat) : sle :=
{
  long_chains := (multiset.erase (sle.long_chains G) a),
  long_chains_are_long := begin intros, have H2 : (x ∈ G.long_chains), by exact multiset.mem_of_mem_erase H,
  clear H, have H1 : ∀ x ∈ G.long_chains, x ≥ 3, by exact G.long_chains_are_long, finish, end,
  long_loops := (sle.long_loops G),
  long_loops_are_long_and_even := G.long_loops_are_long_and_even
}

#check multiset.mem_of_mem_erase

def rem_loop_from_sle (G : sle) (a:nat) : sle :=
{
  long_chains := (sle.long_chains G),
  long_chains_are_long := G.long_chains_are_long,
  long_loops := (multiset.erase (sle.long_loops G) a),
  long_loops_are_long_and_even := begin intros, split, have H1 : (x ∈ G.long_loops),
  by exact multiset.mem_of_mem_erase H, have H2 : ∀ x ∈ G.long_loops, x ≥ 4 ∧ 2 ∣ x,  by exact G.long_loops_are_long_and_even,
   finish, have H1 : (x ∈ G.long_loops),
  by exact multiset.mem_of_mem_erase H, have H2 : ∀ x ∈ G.long_loops, x ≥ 4 ∧ 2 ∣ x,  by exact G.long_loops_are_long_and_even,
   finish, end
} 



def size_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G)


def squnum (G : simple_loony_endgame): nat := 
multiset.fold (nat.add) 0 (all_chains G) + multiset.fold (nat.add) 0 (all_loops G)




def size (e : sle) : ℕ := multiset.card e.long_chains + multiset.card e.long_loops


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

#eval chain_move_values {3,4,5,6,3,3,3,3}

def loop_move_values (s0 : multiset ℕ) : multiset ℕ := 
multiset.pmap (λ (a : ℕ) (h : a ∈ s0), a - 4 + int.nat_abs (4 - loop_value (s0.erase a))) s0 (λ a,id)



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

definition value1 (G : sle) := value_aux G.long_chains G.long_loops

definition value (G : simple_loony_endgame) := value_aux (all_chains G) (all_loops G)

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


def distel (m : multiset nat): nat := multiset.card (multiset.erase_dup (m))


def fcv_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G) 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_chains G)) + 1)*4 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_loops G)) + 2)*8 

def fcv (G : sle):= multiset.card G.long_chains + multiset.card G.long_loops - (distel (G.long_chains))*4 
- (distel (G.long_loops))*8 

def tb_G (G : simple_loony_endgame)  :=
if size_G G = 0 then 0
else if multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (simple_loony_endgame.long_loops G) + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G = 0 then 4
else if simple_loony_endgame.long_chains G = multiset.zero then 6
else 4

def tb (G : sle)  :=
if size G = 0 then 0
else if  G.long_loops = multiset.zero then 8
else if  G.long_chains = multiset.zero then 4
--else if (multiset.count 3 G.long_chains) = (multiset.card G.long_chains) then 6
else if multiset.erase_dup (G.long_chains) = {3} then 6
else 4

#check game_three_succ empty_game

#check game_long_loop_succ empty_game 8 


#check min 1 2



def cv_G (G : simple_loony_endgame) := fcv_G G + tb_G G

def cv (G : sle) := fcv G + tb G

#check 4 % 1

def loop_move_is_optimal (G : simple_loony_endgame) (a: nat): Prop  :=
value G = a - 4 + int.nat_abs (4 - value_aux (all_chains G) ((all_loops G).erase a))

def chain_move_is_optimal (G : simple_loony_endgame) (a: nat): Prop  :=
value G = a - 2 + int.nat_abs (2 - value_aux ((all_chains G).erase a) (all_loops G))

--set_option class.instance_max_depth

/-def v_G (G : simple_loony_endgame):  simple_loony_endgame → int
| x := if h : x = empty_game then 0 else if i : x =  (game_three_succ G) then (min (v_G G - 3) (2 - 3 - (v_G G))) else 
if j : x = (game_four_succ G) then 
have size_G G < size_G x, from begin rw[j], unfold game_four_succ, unfold simple_loony_endgame.sizeof,   end,

(min (v_G G - 4) ( - (v_G G)))

else if k : x = (game_six_succ G) then (min (v_G G - 6) (4 - 6 - v_G G)) 
else if l : ∃ (n : nat) (Hn : n ≥ 4), x = (game_long_chain_succ G n Hn) then (min ((v_G G) - n) (2 - n - v_G G)) /-
else if o (m : nat) (Hm : n ≥ 8 ) (Pm : 2 ∣ n) : x = (game_long_loop_succ G m Hm Pm) then (min ((v_G G) - m) (4 - m - v_G G)) -/
/-else sorry 
 using_well_founded {rel_tac :=
    λ _ _, `[exact ⟨_, measure_wf size_G⟩]}-/


--| empty_game := 0
--| (game_three_succ G) := (min (v_G G - 3) (2 - 3 - (v_G G))
--| (game_four_succ G) := (min (v_G G - 4) (- (v_G G))
--| (game_six_succ G) := (min (v_G G - 6) (4 - 6 - v_G G))
--| (game_long_chain_succ G n Hn) := (min ((v_G G) - n) (2 - n - v_G G))
--| (game_long_loop_succ G m Hm Pm) := (min ((v_G G) - m) (4 - m - v_G G)) ­-/

---------------------------------------------------------------------------------------------------------------
--------------------------------------------------theorems-----------------------------------------------------
open multiset 
#check @strong_induction_on 
#print prefix multiset.strong_induction_on 

theorem strong_induction_eq {α : Type} {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]

@[simp] lemma v_empty : value_aux 0 0 = 0 :=
 begin
  unfold value_aux, -- strong_induction hell
  rw strong_induction_eq, -- goal now one page long
  rw strong_induction_eq, -- goal now two pages long
  simp,
 end 


lemma v_one_chain (c : ℕ) (h : c ≥ 3) : value_aux (c :: 0) 0 = c :=
 begin
  unfold value_aux,
  rw strong_induction_eq,
  rw strong_induction_eq,
  simp,
  rw strong_induction_eq,
  rw strong_induction_eq,
  simp,
  show 2 + (c - 2) = c,
  rw add_comm,refine nat.sub_add_cancel _,
  exact le_trans (show 2 ≤ 3, by exact dec_trivial) h,
 end


lemma one_comp_case (G : simple_loony_endgame) : ((size_G G) = 1) → (cv_G G = value G) :=
begin
intros, unfold cv_G, unfold fcv_G, unfold size_G at a, rw[a], unfold value, unfold value_aux, unfold tb_G, 
rw strong_induction_eq, rw strong_induction_eq, simp, sorry
end

lemma loop_and_three_chain_case (G : simple_loony_endgame) : (G.three_chains = 1) → (multiset.card(all_loops G) = 1 ) 
→ (cv_G G = value G) := sorry

lemma three_point_one (G : simple_loony_endgame) : ((size_G G) > 0) → (G.three_chains = 0) → (G.four_loops = 0) →  
(value G ≥ 2) := sorry

theorem one_point_three (G : simple_loony_endgame) : (value G ≥ 3 ) ↔ ((cv_G G ≥ 3) ∨ (((G.three_chains = 0 ∧ squnum G = 2 % 4 )
 ∨ (G.three_chains = 1 ∧ squnum G = 3 % 5)) ∧ (((cv_G G + 4*G.four_loops < 2) ∧ (G.four_loops = 0 % 2 )) 
 ∨ ((cv_G G + 4*G.four_loops > 2) ∧ ((G.four_loops = 3 % 8) ∨ (G.four_loops = 4 % 8) ∨ (G.four_loops = 5 % 8) ) ) ))) :=
sorry

theorem two_point_two (G : simple_loony_endgame) : (cv_G G ≥ 2) → (size_G G ≥ 2) → ¬ ((G.three_chains = 1) 
∧ (multiset.card(all_loops G) = 1)) → (value G = cv_G G):= sorry

theorem two_point_one_ad (G : sle) : (cv G ≥ 2) → (size G ≥ 2) → ¬ ((count 3 G.long_chains = 1) 
∧ (card (G.long_loops) = 1)) → (( ∃ C ∈ (G.long_chains), (tb (rem_chain_from_sle G C) = tb G) ∧ (cv (rem_chain_from_sle G C) ≥ 2) ) 
∨ ( ∃ L ∈ (G.long_loops), (tb (rem_loop_from_sle G L) = tb G) ∧ (cv (rem_loop_from_sle G L) ≥ 4))) := sorry

lemma three_point_two (G: simple_loony_endgame) : ((size_G G) > 0) → (cv_G G < 2) → (value G ≤ 4) ∧ ((G.three_chains > 0) ∨
(G.four_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops > 0 ∧ (size_G G) > 1) ∨ (G.six_loops ≥ 2 ∧ (size_G G) > 2)) := sorry

lemma three_point_three_f (G: sle) : if mem 3 G.long_chains then value1 G ≤ 3 ∧ value1 (rem_chain_from_sle G 3) ≤ 4 
else if mem 4 G.long_loops then value1 (rem_loop_from_sle G 4) ≤ 5 else  value1 (rem_loop_from_sle G 6) ≤ 4 := sorry


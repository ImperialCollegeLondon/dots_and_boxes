import data.list.basic tactic.linarith
import tactic.omega tactic.apply
import sle.lemmas
import tactic.fin_cases

open list

-- changing one element of a list by at most d
/--Two lists that are equal except one entry differs by at most d-/
structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d)



/--Two lists that are equal except one entry differs by at most d have equal length-/
theorem eq_size_of_modify_list {l1 l2 : list ℤ } {d : ℤ} (h : list.modify l1 l2 d) : l1.length = l2.length :=
begin
  -- split list.modify condition into its statements
  cases h, 
  -- as the lists below are equal by h_heq, their length must be equal
  have P : length(remove_nth l1 h_n) = length(remove_nth l2 h_n), 
  rw h_heq, 
  rw length_remove_nth l1 h_n h_ha at P, 
  rw length_remove_nth l2 h_n h_hb at P,  
  --need this for finish to work
  have Q : ¬ h_n < 0, simp,
  -- Now  P gives the result by cancelling -1 on both sides, but this
  -- only works if both lists have length > 0. Hence split into easy cases 
  -- and let Lean do the rest
  cases l1, dsimp at h_ha,
  exfalso, finish,
  cases l2, dsimp at h_hb,
  exfalso, finish, 
  finish, 
  end




/--Two lists that are equal except one entry differs by at most d are element
wise equal in all entries except the one at which they differ-/
theorem list.modify_same {A : list ℤ} {B : list ℤ} {d : ℤ}
  (h : list.modify A B d) (m : ℕ) (hmA : m < A.length) (hmB : m < B.length)
  (hmn : h.n ≠ m) : A.nth_le m hmA = B.nth_le m hmB :=
begin
  have H : length A = length B, exact eq_size_of_modify_list h,
  cases h, rw remove_nth_eq_nth_tail at h_heq, rw modify_nth_tail_eq_take_drop at h_heq,
  rw remove_nth_eq_nth_tail at h_heq, rw modify_nth_tail_eq_take_drop at h_heq,
  have p : length (tail (drop h_n A)) = length (tail (drop h_n B)), rw length_tail,
  rw length_tail, rw length_drop, rw length_drop,
  rw H, 
  have h_eq_left : take h_n A = take h_n B , exact append_inj_right' h_heq p,
  have h_eq_right : tail (drop h_n A) = tail (drop h_n B), exact append_inj_left' h_heq p,
  
  rw ← head_reverse_take, rw ← head_reverse_take, 

  have m_cases : (m+1) ≤ h_n ∨ h_n < (m+1) , exact le_or_lt (m + 1) h_n,
  cases m_cases, 
  rw take_lemma m_cases h_eq_left,

  rw nat.lt_iff_add_one_le at hmA, simp at hmn,
  have h1 : 1 ≤ m,
  cases m,
  exfalso,
  have hn_0 : h_n = 0, rw nat.lt_add_one_iff at m_cases,
  exact nat.eq_zero_of_le_zero m_cases,
  exact false.elim (hmn hn_0),
  exact dec_trivial,
  rw take_drop_head_eq h1 hmA,
  clear hmB,
  have hmB: m + 1 ≤ length B, rw ←  H, exact hmA,
  rw take_drop_head_eq h1 hmB,
  have P : tail (drop (m - 1) A) = tail (drop (m - 1) B),
  {
   rw tail_drop,
   rw tail_drop,
   rw tail_drop at h_eq_right,
   rw tail_drop at h_eq_right,
   have h2 : nat.succ h_n ≤ nat.succ (m-1),
   rw nat.succ_le_succ_iff,
   rw nat.lt_add_one_iff at m_cases,
   apply nat.le_pred_of_lt,
   exact lt_of_le_of_ne' m_cases hmn, 

   exact drop_lemma h2 h_eq_right,
  },
  rw P,

  refl,refl,

  
end


/--list.modify is symmetric-/
def list.modify.symm (A B : list ℤ) (d : ℤ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  bound := by rw [←neg_sub, abs_neg]; exact m.bound
}

-- proposal : define a game to be 
/-
1) a size s (number of lists -- two in our case)
2) list of the tf's (list of nats of size s)
3) a function from `fin s` to `list ℕ` or `list ℤ` or whatever

Define game.modify of two games G1 and G2 to be:

1) i : fin s
2) Proof that the j'th lists are equal if j ≠ i
3) n : fin (length of i'th list)
4) proof that i'th lists are equal away from n'th place
5) Proove that values of n'th place of i'th list differ by at most d.

Note: will now need to redefine game.value :-(

structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d)

-/
/-- abstract game with n types of list as components -/
structure game (n : ℕ) :=
(f : fin n → list ℤ)

namespace game
@[ext] def ext {n : ℕ} (G1 G2 : game n) : (∀ (i : ℕ) (hi : i < n), G1.f ⟨i, hi⟩ = G2.f ⟨i, hi⟩) → G1 = G2 :=
begin
  intro h,
  cases G1, cases G2,
  rw mk.inj_eq,
  funext j,
  cases j with i hi,
  apply h,
end

/--Two games that are equal except one entry in one sublist of components differs by at most d-/
structure modify {n : ℕ} (G1 G2 : game n) (d : ℤ) :=
(j : fin n)
(hj : ∀ i : fin n, i ≠ j → G1.f i = G2.f i)
(hl : list.modify (G1.f j) (G2.f j) d)

/--the empty game / completed game-/
def zero (n : ℕ): game n:=
{
  f := λ (i : fin n), nil
}



/--the size of a game with only chains and loops-/
def size2 (G : game 2) : ℕ := 
length (G.f (0:fin 2)) + length (G.f (1:fin 2)) 

/--The number of components of a game-/
def size {n : ℕ} (G : game n) : ℕ := 
list.sum (list.of_fn (λ i, (G.f i).length))

/--For a game with only chains and loops the definitions 
of the size, size and size2, are equivalent-/
theorem size_eq_size2 (G : game 2) : G.size = G.size2 :=
begin
  show (0 + _) + _ = _ + _,
  rw zero_add,
  refl,
end

/--The size2 of the empty game is 0-/
lemma size2_zero : (zero 2).size2 = 0 := rfl

/--If size2 of a game is 0, it is the empty game-/
lemma eq_zero_of_size2_zero (G : game 2) : G.size2 = 0 → G = zero 2 :=
begin
  intro h,
  replace h := nat.eq_zero_of_add_eq_zero h,
  unfold zero,
  cases h with h1 h2,
  rw length_eq_zero at h1 h2,
  cases G,
  apply game.ext,
  intros i hi,
  set i0 : fin 2 := ⟨i, hi⟩,
  fin_cases i0; rw h,
    exact h1,
    exact h2,
end

/--For two games that are equal except one entry in one sublist of components differs by at most d 
all pairwise corresponding sublists have equal length-/
lemma eq_list_lengths_of_modify {n : ℕ} {G1 G2 : game n} {d : ℤ} (h : modify G1 G2 d):
∀ (i : fin n), length (G1.f i) = length (G2.f i) :=
begin
cases h with j heq modi, 
intro i,
by_cases p1 : i ≠ j,
rw heq i p1,
push_neg at p1,
rw ← p1 at modi,
exact eq_size_of_modify_list modi,
end


end game

open game

def list.min {X : Type*} [decidable_linear_order X] :
Π (L : list X), (L ≠ []) → X
| ([]) hL := false.elim $ hL rfl
| (x :: []) hL := x
| (x :: y :: L) _ := min x (list.min (y :: L) dec_trivial)

def list.min' (L : list ℤ) : ℤ :=
if h : L = [] then 0 else list.min L h

def game.rec_on_size2' (C : game 2→ Sort*) :
(∀ G : game 2, G.size2 = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game 2, G.size2 = m → C G := λ z ih n, nat.rec z ih n

universe u
--@[elab_as_eliminator]
def game.rec_on_size2 {C : game 2 → Sort u} :
C (game.zero 2) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ G : game 2, C G :=
λ z ih G, @game.rec_on_size2' C (λ H hH, (by rwa eq_zero_of_size2_zero _ hH : C H)) ih (G.size2) _ rfl

/-- Let G be all chains or loops. If m is a component of G, and
  vL = value of game G with m removed, list.aux_fun this is the value of G given
  that we're playing m -/
def list.aux_fun (m tf vL : ℤ) := m - tf + abs(tf - vL)

theorem list.aux_fun_L1 {m1 m2 tf vL d : ℤ} (hm : abs (m1 - m2) ≤ d) :
  abs(list.aux_fun m1 tf vL - list.aux_fun m2 tf vL) ≤ d :=
begin
  unfold list.aux_fun, finish,
end

theorem list.aux_fun_L2 {m tf vL1 vL2 d : ℤ} (hm : abs (vL1 - vL2) ≤ d) :
  abs(list.aux_fun m tf vL1 - list.aux_fun m tf vL2) ≤ d :=
begin
 unfold list.aux_fun, rw sub_add_eq_sub_sub_swap, 
 have Q: abs(tf - vL1 - (tf - vL2)) ≤ d, 
 show abs (tf + -vL1 + -(tf + -vL2)) ≤ d,
 rw add_comm tf, rw add_assoc, show abs (-vL1 + (tf - (tf + -vL2))) ≤ d,
 rw sub_add_eq_sub_sub tf, show abs (-vL1 + (tf + - tf - -vL2)) ≤ d,
 rw add_neg_self tf , rw ←  abs_neg, finish,  
 
 rw add_comm, show abs (abs (tf + -vL1) + (m + -tf) + -abs (tf + -vL2) + -(m + -tf)) ≤ d,
 rw add_assoc,rw add_assoc, 
 rw add_comm (m + -tf), rw add_assoc, rw add_comm (-(m+-tf)),
 rw add_neg_self (m+-tf), rw add_zero, 
 have R: abs (abs (tf - vL1) - abs (tf - vL2)) ≤ abs ((tf - vL1) - (tf - vL2)),
 exact abs_abs_sub_abs_le_abs_sub (tf - vL1) (tf - vL2),
 exact le_trans R Q,
end

lemma abs_min_sub_min {a b x y d : ℤ} (hab : abs (a - b) ≤ d)
  (hxy : abs (x - y) ≤ d) : abs (min a x - min b y) ≤ d :=
begin
  rw abs_le at *,
  cases hab; cases hxy,
  unfold min,
  split_ifs; split; linarith,
end

-- need this for list.min'
theorem list.min_change (L M : list ℤ) (hL : L ≠ []) (hLM : L.length = M.length) (hM : M ≠ []) (d : ℤ)
(hdist : ∀ (i : ℕ) (hiL : i < L.length) (hiM : i < M.length), abs (L.nth_le i hiL - M.nth_le i hiM) ≤ d) :
  abs (L.min hL - M.min hM) ≤ d :=
begin
  show abs (list.min L hL - list.min M hM) ≤ d,
  revert M,
  cases L with n L,
    contradiction,
  revert n,
  induction L with n1 L IH,
  {
    intros n _ M hM1 _ hi,
    change 1 = length M at hM1,
    symmetry' at hM1,
    rw length_eq_one at hM1,
    cases hM1 with m hM1,
    simp only [hM1],
    show abs (n - m) ≤ d,
    convert hi 0 (zero_lt_one) _,
    simp only [hM1],
    refl,
    rw hM1,
    exact zero_lt_one,
  },
  { intros n _ M hM _ hi,
    cases M with m M, cases hM,
    cases M with m1 M, cases hM,
    unfold list.min,
    have hmn : abs (n - m) ≤ d,
      exact hi 0 dec_trivial dec_trivial,
    replace hM := nat.succ_inj hM,
    have hyp : (∀ (i : ℕ) (hiL : i < length (n1 :: L)) (hiM : i < length (m1 :: M)),
      abs (nth_le (n1 :: L) i hiL - nth_le (m1 :: M) i hiM) ≤ d),
      intros i hiL hiM,
      exact hi (i + 1) (nat.succ_lt_succ hiL) (nat.succ_lt_succ hiM),
    have h := IH n1 dec_trivial (m1 :: M) hM dec_trivial hyp,
    exact abs_min_sub_min hmn h}
end



lemma list.min'_change (L M : list ℤ) (hLM : L.length = M.length) (d : ℤ) (hd : 0 ≤ d)
(hdist : ∀ (i : ℕ) (hiL : i < L.length) (hiM : i < M.length), abs (L.nth_le i hiL - M.nth_le i hiM) ≤ d) :
  abs (L.min' - M.min') ≤ d := 
  begin
  cases M with m Mn,
  simp at *,
  rw length_eq_zero at hLM,
  rw hLM,
  unfold list.min',

  simp *,
  have hM : ¬ (m :: Mn : list ℤ) = nil := by simp,
  have hL : ¬ L = nil, 
  apply ne_nil_of_length_pos,
  rw hLM,
  exact length_pos_of_ne_nil hM,

  
  unfold list.min',
  split_ifs,
  apply list.min_change,
  exact hLM,
  exact hdist,

  end

/-- Value of all-chain or all-loop game L given that we're playing in i'th component -/
definition list.value_i (tf : ℤ) :
  ∀ (n : ℕ) (L : list ℤ) (i : fin n) (hL : L.length = n), ℤ
| (0) L i h := begin exfalso,  exact fin.elim0 i, end -- i gives a contradiction
| (d + 1) L i h := list.aux_fun (L.nth_le i.val (by rw h; exact i.is_lt)) tf (list.min' (list.of_fn $
    λ (j : fin d), list.value_i d (L.remove_nth i.val) j begin
      rw list.length_remove_nth L i.val _,
        rw h, simp,
      rw h, exact i.is_lt,
    end))

/-
#eval list.value_i 4 3 [4,4,10] ⟨1, by norm_num⟩ sorry 

#check list.modify
lemma list.modify_to_list.remove.modify (A B : list ℤ) (d : ℤ): 
Π (h : list.modify A B d), Π (m : ℕ), m ≠ h.n → m < A.length 
→ list.modify (A.remove_nth m) (B.remove_nth m) d :=
begin
intros h m hm m_lt, 
have H : length A = length B, exact eq_size_of_modify_list A B d h,
cases h, split,
sorry,
sorry,
-- should do cases h_n somewhere
exact (h_n-1),
rw length_remove_nth,
rw ← nat.pred_eq_sub_one h_n,
rw ← nat.pred_eq_sub_one (length A),
apply nat.pred_lt_pred, sorry,
exact h_ha,
exact m_lt,
rw length_remove_nth,
rw ← nat.pred_eq_sub_one h_n,
rw ← nat.pred_eq_sub_one (length B),
apply nat.pred_lt_pred, sorry,
exact h_hb,
rw ← H,
exact m_lt,

 

end

-/

set_option trace.check true

/-- Man in the middle for all-chain or all-loop situations -/
theorem MITM_baby (tf : ℤ) (L1 L2 : list ℤ) (d : ℤ) (h : list.modify L1 L2 d)
  (n : ℕ) (hL1 : L1.length = n) (hL2 : L2.length = n) (i : fin n) :
  abs (list.value_i tf n L1 i hL1 - list.value_i tf n L2 i hL2) ≤ d :=
begin
  revert L1 L2,
  induction n with e he,
    cases i, cases i_is_lt,
  intros L1 L2 h hL1 hL2,
  unfold list.value_i,
  by_cases hin : h.n = i.val,
  { -- i = place where lists differ
    have heq := h.heq,
    rw hin at heq,
    simp only [heq],
    apply list.aux_fun_L1,
    convert h.bound,
      exact hin.symm,
      exact hin.symm,
  },
  { -- i ≠ place where lists differ
    rw list.modify_same h i.val _ (begin rw hL2, exact i.is_lt end) hin,
    apply list.aux_fun_L2,
    -- apply "lists differ by at most d -> min differs by at most d"
    apply list.min'_change,
      simp only [list.length_of_fn],
    intros,
    -- now deduce from he somehow!
    --prove 0 <= d from h using that the asolute value is non-negative
    cases h, apply le_trans _ h_bound, 
    show abs (nth_le L1 h_n h_ha - nth_le L2 h_n h_hb) ≥ 0,
    exact abs_nonneg _,

    intros n HnL HnM,
    cases h,
    --need this as argument for he (in he L1 = (remove_nth L1 (i.val))
    --and L2 = (remove_nth L2 (i.val)))
    have i_cases : i.val < h_n ∨ i.val = h_n ∨ h_n < i.val, exact lt_trichotomy i.val h_n,
    have P : list.modify (remove_nth L1 (i.val)) (remove_nth L2 (i.val)) d:=
    --the point at which both lists will differ is h_n-1 if h_n > i.val
    --and h_n if h_n < i.val
    {n:= if i.val < h_n then h_n-1 else h_n,
     ha:=begin  
         rw list.length_remove_nth,
         split_ifs,
         show (h_n - 1) < (length L1 - 1),
         rw nat.sub_lt_left_iff_lt_add,
         rw add_comm,
         rw nat.sub_add_cancel _,
         exact h_ha,
         rw hL1,
         exact dec_trivial,
         exact nat.one_le_of_lt h,
         cases i_cases,
         exact false.elim (h i_cases),
         cases i_cases,
         rw eq_comm at i_cases,
         exact false.elim (hin i_cases),
         show h_n < (length L1 - 1),
         rw hL1,
         have s: i.val ≤ nat.succ e - 1,
         apply nat.le_pred_of_lt i.is_lt,
         exact nat.lt_of_lt_of_le i_cases s,
         rw hL1, exact i.is_lt,
         end,
     hb:=begin 
         rw list.length_remove_nth,
         split_ifs,
         show (h_n - 1) < (length L2 - 1),
         rw nat.sub_lt_left_iff_lt_add,
         rw add_comm,
         rw nat.sub_add_cancel _,
         exact h_hb,
         rw hL2,
         exact dec_trivial,
         exact nat.one_le_of_lt h,
         cases i_cases,
         exact false.elim (h i_cases),
         cases i_cases,
         simp at hin,
         rw eq_comm at i_cases,
         exact false.elim (hin i_cases),
         show h_n < (length L2 - 1),
         rw hL2,
         have s: i.val ≤ nat.succ e - 1,
         apply nat.le_pred_of_lt i.is_lt,
         exact nat.lt_of_lt_of_le i_cases s,
         rw hL2, exact i.is_lt,
         end,
     heq:=begin
          
          split_ifs,
          have Q : 1 ≤ h_n,
          exact nat.one_le_of_lt h,
          --repeat {rw remove_nth_eq_nth_tail, rw modify_nth_tail_eq_take_drop},
          rw remove_nth_remove_nth L1,
          rw remove_nth_remove_nth L2,
          split_ifs,         
          rw nat.sub_add_cancel,
          rw h_heq,
          exact Q,
          exfalso,
          rw nat.sub_add_cancel at h_1,
          exact false.elim(h_1 h),
          exact Q,
          rw hL2,
          exact nat.le_of_lt i.is_lt,
          apply nat.le_of_lt,
          rw nat.sub_add_cancel Q,
          exact h_hb,
          rw hL1,
          exact nat.le_of_lt i.is_lt,
          apply nat.le_of_lt,
          rw nat.sub_add_cancel Q,
          exact h_ha,
          
          rw remove_nth_remove_nth L1,
          rw remove_nth_remove_nth L2,
          split_ifs,     
          exfalso,
          cases i_cases,
          exact false.elim (h i_cases),
          cases i_cases,
          simp at hin,
          rw eq_comm at hin,
          exact false.elim (hin i_cases),
          rw nat.lt_iff_le_not_le at h_1,
          have h_2 : h_n + 1 ≤ i.val,
          rw ← nat.succ_eq_add_one h_n,
          apply nat.succ_le_of_lt,
          exact i_cases,
          exact false.elim (h_1.right h_2),    
          rw h_heq,
          rw hL2,
          exact nat.le_of_lt i.is_lt,
          exact nat.succ_le_of_lt h_hb,
          rw hL1,
          exact nat.le_of_lt i.is_lt,
          exact nat.succ_le_of_lt h_ha,
          end,
     bound:=begin 
            split_ifs,
              have Q : 1 ≤ h_n := by exact nat.one_le_of_lt h,
              rw nth_le_remove_nth,
              rw nth_le_remove_nth,
              rw if_pos,
              rw if_pos,
              simp only [nat.sub_add_cancel Q],
              exact h_bound,
              exact nat.le_pred_of_lt h,
              exact nat.le_pred_of_lt h,
              rw nat.sub_add_cancel Q,
              exact h_hb,
              rw nat.sub_lt_left_iff_lt_add,
              apply nat.lt_trans h_hb,
              simp,
              exact Q,
              rw nat.sub_add_cancel Q,
              exact h_ha,
              rw nat.sub_lt_left_iff_lt_add,
              apply nat.lt_trans h_ha,
              simp,
              exact Q,


              rw nth_le_remove_nth,
              rw nth_le_remove_nth,
              rw if_neg,
              rw if_neg,
              exact h_bound,
              simp at hin,
              rw le_iff_eq_or_lt,
              intro neg,
              cases neg,
              rw eq_comm at neg,
              exact false.elim(hin neg),
              exact false.elim(h neg),

              simp at hin,
              rw le_iff_eq_or_lt,
              intro neg,
              cases neg,
              rw eq_comm at neg,
              exact false.elim(hin neg),
              exact false.elim(h neg),

              push_neg at h,
              rw hL2,
              apply nat.succ_lt_succ,
              cases i_cases,
              exfalso,
              exact nat.lt_le_antisymm i_cases h,
              cases i_cases,
              simp at hin,
              rw eq_comm at i_cases,
              exact false.elim (hin i_cases),
              exact lt_trans_of_succ i_cases i.is_lt,
              

              push_neg at h,
              rw hL1,
              apply nat.succ_lt_succ,
              cases i_cases,
              exfalso,
              exact nat.lt_le_antisymm i_cases h,
              cases i_cases,
              simp at hin,
              rw eq_comm at i_cases,
              exact false.elim (hin i_cases),
              exact lt_trans_of_succ i_cases i.is_lt,

            end,

    


    },

    -- prove PL1 : length (remove_nth L1 (i.val)) = e, 
    -- and PL2 : length (remove_nth L2 (i.val)) = e to use as arguments for he
    have PL1 : length (remove_nth L1 (i.val)) = e,
      rw length_remove_nth,
      rw hL1,
      rw nat.succ_eq_add_one,
      rw nat.add_sub_cancel,
      rw hL1,
      exact i.is_lt,

    have PL2 : length (remove_nth L2 (i.val)) = e,
      rw length_remove_nth,
      rw hL2,
      rw nat.succ_eq_add_one,
      rw nat.add_sub_cancel,
      rw hL2,
      exact i.is_lt,
    rw length_of_fn at HnL HnM,
    rw nth_le_of_fn _ ⟨n, HnL⟩,
    rw nth_le_of_fn _ ⟨n, HnM⟩,
    apply he,
    exact P,
    }
end

-- proposal : define a game to be 
/-
1) a size s (number of lists -- two in our case)
2) list of the tf's (list of nats of size s)
3) a function from `fin s` to `list ℕ` or `list ℤ` or whatever

Define game.modify of two games G1 and G2 to be:

1) i : fin s
2) Proof that the j'th lists are equal if j ≠ i
3) n : fin (length of i'th list)
4) proof that i'th lists are equal away from n'th place
5) Proove that values of n'th place of i'th list differ by at most d.

Note: will now need to redefine game.value :-(
-/

/-- Remove i'th element of j'th component of G -/
def game.remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) : game 2 :=
{f := λ k, if h : k = j then list.remove_nth (G.f j) i.val else (G.f k)}

lemma game.size2_remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) :
  (G.remove j i).size2 = G.size2 - 1 :=
begin
  fin_cases j,
  { show _ + _ = _ + _ - 1,
    unfold game.remove,
    dsimp,
    split_ifs,
    { cases h_1},
    { rw length_remove_nth _ _ i.is_lt, 
      show length (G.f 0) - 1 + length (G.f 1) = 
        length (G.f 0) + length (G.f 1) - 1,
      have i2 := i.is_lt,
      change i.val < length (G.f 0) at i2,
      generalize hm : length (G.f 0) = m,
      rw hm at i2,
      cases m with m,
        cases i2,
      generalize hm2 : length (G.f 1) = m2,
      clear i2 i hm hm2 G,
      omega},
    { cases h_1},
    { exfalso, apply h, refl},
  },
  { show _ + _ = _ + _ - 1,
    unfold game.remove,
    dsimp,
    split_ifs,
    { cases h},
    { cases h},
    { rw length_remove_nth _ _ i.is_lt,
      show length (G.f 0) + (length (G.f 1) - 1) = 
        length (G.f 0) + length (G.f 1) - 1,
      have i2 := i.is_lt,
      change i.val < length (G.f 1) at i2,
      generalize hm : length (G.f 1) = m, rw hm at i2,
      generalize hm2 : length (G.f 0) = m2,
      cases m with m,
        cases i2,
      clear i2 i hm hm2 G,
      omega},
    { exfalso, apply h_1, refl}
  }
end

lemma game.remove_of_modify {G1 G2 : game 2} {d : ℤ }:
modify G1 G2 d → ∀ (j : fin 2) (i1 : fin (G1.f j).length)
(i2 : fin (G2.f j).length) (hi : i1.val = i2.val), 
modify (G1.remove j i1) (G2.remove j i2) d :=
begin
intros h j i1 i2 hi,
split,
swap 3, {exact h.j},
{intros x x_neq,
unfold game.remove,
dsimp,
split_ifs,
{rw hi,
rw h_1 at x_neq,
rw h.hj j x_neq},
{ exact h.hj x x_neq,},
  },
{
  unfold game.remove,dsimp,
  split_ifs,
  {rw hi, 
  rw eq_comm at h_1,
  simp only [h_1],
  have h_lmod : list.modify (G1.f (h.j)) (G2.f (h.j)) d := by exact h.hl,
  by_cases hn : i2.val < h_lmod.n,
  {split,swap 3,
  {exact (h_lmod.n-1)},
  {rw remove_nth_remove_nth,
  {split_ifs,
  {rw nat.sub_add_cancel,
   rw h_lmod.heq, 
   rw remove_nth_remove_nth,
   split_ifs,
   {exfalso,exact nat.lt_le_antisymm h_3 hn},
   {refl,},
   {exact le_of_lt h_lmod.hb},
   {sorry},
   {sorry},},
  {sorry,},},

   
   sorry,sorry,},
   {sorry,},
   {sorry,},
   {sorry,},
  },
  
  {split,swap 3,
  {sorry},
  {rw remove_nth_remove_nth,
   sorry,sorry,sorry},
   {sorry,},
   {sorry,},
   {sorry,},
  },
  },exact h.hl},

end

lemma modify.symm {G1 G2 : game 2} {d : ℤ} 
(m : modify G1 G2 d) : modify G2 G1 d :=
{ j := m.j,
  hj := begin intros i h, rw eq_comm, exact m.hj i h, end,
  hl := begin apply list.modify.symm, exact m.hl, end,
}

lemma game.remove_of_modify_symm {G1 G2 : game 2} {d : ℤ }:
modify G1 G2 d → ∀ (j : fin 2) (i1 : fin (G1.f j).length)
(i2 : fin (G2.f j).length) (hi : i1.val = i2.val), 
modify (G2.remove j i2) (G1.remove j i1) d :=
begin 
intros a b c d e,
apply modify.symm,
exact game.remove_of_modify a b c d e,
end

def game.value : game 2 → ℤ := @game.rec_on_size2 (λ G, ℤ) (0 : ℤ) $ λ n hn G hG,
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
      hn (G.remove j i) (by rw [game.size2_remove, hG, nat.add_sub_cancel])) 
  ))
  begin
    intro h,
    rw [←list.length_eq_zero, list.length_bind] at h,
    dsimp at h,
    rw [list.length_of_fn, list.length_of_fn] at h,
    change size G = 0 at h,
    rw [size_eq_size2, hG] at h,
    revert h, exact dec_trivial,
  end

theorem game.value_def (G : game 2) (n : ℕ) (hG : G.size2 = nat.succ n):
  game.value G =
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
  game.value (G.remove j i))))
  begin
    intro h,
    rw [←list.length_eq_zero, list.length_bind] at h,
    dsimp at h,
    rw [list.length_of_fn, list.length_of_fn] at h,
    change size G = 0 at h,
    rw [size_eq_size2, hG] at h,
    revert h, exact dec_trivial,
  end
:=
begin
  unfold game.value,
  unfold game.rec_on_size2,
  unfold game.rec_on_size2',
  simp only [hG],
  congr',
  ext i n0 n1,
  congr',
  ext j,
  congr',
  rw game.size2_remove,
  rw hG,
  exact (nat.add_sub_cancel n 1).symm
end

theorem list.bind_fin2 {α : Type*} (f : fin 2 → list α) : 
  list.bind [0, 1] f = f 0 ++ f 1 :=
begin
  show f 0 ++ (f 1 ++ nil) = f 0 ++ f 1,
  rw append_nil,
end

theorem eq_size_of_modify {G1 G2 : game 2} {d : ℤ} (h : game.modify G1 G2 d) : G1.size2 = G2.size2 :=
begin
  cases h with j hj hjm, 
  unfold size2,
  fin_cases j,
  { have h0 := eq_size_of_modify_list hjm, 
    change length (G1.f 0) = length (G2.f 0) at h0,
    have h1 : G1.f 1 = G2.f 1,
      exact hj ⟨1, dec_trivial⟩ dec_trivial,
    rw [h0, h1],
  },
  {
    have h0 := eq_size_of_modify_list hjm, 
    change length (G1.f 1) = length (G2.f 1) at h0,
    have h1 : G1.f 0 = G2.f 0,
      exact hj ⟨0, dec_trivial⟩ dec_trivial,
    rw [h0, h1],
  }
end




#exit

-- this is the big challenge
theorem MITM (G1 G2 : game 2) (d : ℤ) (h1 : game.modify G1 G2 d) (h2 : 0 ≤ d):
 abs(G1.value - G2.value) ≤ d :=
begin
  revert G1,
  revert G2,
  apply @game.rec_on_size2 (λ G2, ∀ G1, modify G1 G2 d → 
  abs (game.value G1 - game.value G2) ≤ d),
  -- this might be tricky!
  { intros G h1, have h3 : G.size2 = (zero 2).size2 := eq_size_of_modify h1,
  rw size2_zero at h3, have H := eq_zero_of_size2_zero _ h3, 
  rw H, show  0 ≤ d, exact h2},
  { intros n H G1 p G2 p2,
    have hs := eq_size_of_modify p2,
    rw p at hs,
    rw game.value_def _ _ hs,
    rw game.value_def _ _ p,
    apply list.min_change,
    { rw length_bind, dsimp,
      rw [length_of_fn, length_of_fn],
      rw length_bind, dsimp,
      rw [length_of_fn, length_of_fn],
      show G2.size = G1.size,
      rw size_eq_size2,
      rw size_eq_size2,
      rw [p, hs]},
    intros i hiL hiM,
    rw length_bind at hiL hiM, dsimp at hiL hiM,
    rw [length_of_fn, length_of_fn] at hiL_1 hiM_1,
    simp only [list.bind_fin2],
    by_cases hi : i < length (G2.f 0),
    { rw nth_le_append _ _,
      swap,
      { rw length_of_fn,
        exact hi,
      },
      rw nth_le_append _ _,
      swap,
      -- need a theorem which eats p2 : game.modify G1 G2 d and
      -- spits out a proof that length G1.C = length G2.c
      -----Created it. It is called eq_list_lengths_of_modify
      { rw length_of_fn,
        convert hi using 1,
        symmetry,
        apply eq_list_lengths_of_modify p2,
      },
      rw nth_le_of_fn' _ _ hi,
      rw nth_le_of_fn' _ _ _,
      swap, 
      { convert hi using 1,
        symmetry,
        apply eq_list_lengths_of_modify p2,
      },
      by_cases hj : p2.j = 0,
      { set p2l := p2.hl with hp2l,
        set p2n := p2l.n with p2ln,
        by_cases hni : p2n = i,
        { have hG1G2 : game.remove G1 0 ⟨i, begin
            convert hi using 1,
            symmetry,
            apply eq_list_lengths_of_modify p2, 
          end⟩ = game.remove G2 0 ⟨i, hi⟩,
          { apply game.ext,
            intros a ha,
            cases a with a,
            { unfold game.remove,
              dsimp,
              rw dif_pos, swap, refl,
              rw dif_pos, swap, refl,
              rw ←hni,
              rw p2ln,
              convert p2l.heq.symm; rw hj,
            },
            { cases a with a, swap, cases ha, cases ha_a, cases ha_a_a,
              unfold game.remove,
              dsimp,
              rw dif_neg, swap, exact dec_trivial,
              rw dif_neg, swap, exact dec_trivial,
              convert (p2.hj 1 _).symm using 1,
              rw hj,
              exact dec_trivial,
            }
          },
          rw hG1G2,
          convert p2l.bound using 1,
          apply congr_arg,
          dsimp,
          simp only [p2ln.symm, hni, hj],
          ring
        },
        { -- in this case nth_le (G2.f 0) i _ = nth_le (G1.f 0) i _
          -- and we can use the inductive hypothesis-
          -- should use list.modify_same, but duplicates create
          -- problems (come from nth_le as well)
          
          
          --rw hj at p2l,
          have nth_le_eq : nth_le (G2.f 0) i _ = nth_le (G1.f 0) i _,
          apply list.modify_same _ i _ _ _,
          exact d,
          simp only [hj] at p2l,
          exact p2l,
          convert hni,
          rw eq_comm,
          exact hj,
          rw eq_comm,
          exact hj,
          --library_search,
          exact cast_heq
          ((λ (A A_1 : list ℤ) (e_1 : A = A_1) (B B_1 : list ℤ) (e_2 : B = B_1) (d d_1 : ℤ) (e_3 : d = d_1),
              congr (congr (congr_arg list.modify e_1) e_2) e_3)
              (G2.f (p2.j))
              (G2.f 0)
              ((λ (c c_1 : game 2) (e_1 : c = c_1) (a a_1 : fin 2) (e_2 : a = a_1), congr (congr_arg f e_1) e_2) G2 G2
                (eq.refl G2)
                (p2.j)
                0
                hj)
              (G1.f (p2.j))
              (G1.f 0)
              ((λ (c c_1 : game 2) (e_1 : c = c_1) (a a_1 : fin 2) (e_2 : a = a_1), congr (congr_arg f e_1) e_2) G1 G1
                (eq.refl G1)
                (p2.j)
                0
                hj)
              d
              d
              (eq.refl d))
          p2l,--up to here by library_search
          simp only [nth_le_eq],
          
          convert (H (game.remove G2 0 ⟨i, hi⟩) _ (game.remove G1 0 ⟨i, _⟩) (game.remove_of_modify_symm p2 0 ⟨i, hi⟩ ⟨i, _⟩ (by refl))) using 1,
          {apply congr_arg,
          dsimp,
          --simp only [p2ln.symm, hni, hj],
          ring,
          sorry,
          },
          { convert hi using 1,
            symmetry,
            apply eq_list_lengths_of_modify p2,
          },
          { convert hi using 1,
            symmetry,
            apply eq_list_lengths_of_modify p2,
          },
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
          {exact hi,
          },
          

        },
      },
      { have G1G2_1 : G2.f 0 = G1.f 0,
        rw eq_comm at hj,
        exact p2.hj 0 hj,
        simp only [G1G2_1],
        { convert (H (game.remove G2 0 ⟨i, hi⟩) _ (game.remove G1 0 ⟨i, _⟩) (game.remove_of_modify_symm p2 0 ⟨i, hi⟩ ⟨i, _⟩ (by refl))) using 1,
          {apply congr_arg,
          dsimp,
          --simp only [p2ln.symm, hni, hj],
          ring,
          sorry,
          },
          { convert hi using 1,
            symmetry,
            apply eq_list_lengths_of_modify p2,
          },
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },

        },

        },
    },
    { 
      
      push_neg at hi,
      rw nth_le_append_right _ _,
      swap,
      { rw length_of_fn,
        exact hi,
      },
      rw nth_le_append_right _ _,
      swap,
      -- need a theorem which eats p2 : game.modify G1 G2 d and
      -- spits out a proof that length G1.C = length G2.c
      -----Created it. It is called eq_list_lengths_of_modify
      { rw length_of_fn,
        convert hi using 1,
        symmetry,
        apply eq_list_lengths_of_modify p2,
      },
      have hi_new : i - length (G2.f 0) < length (G2.f 1), 
      { sorry
      },
      simp only [length_of_fn],
      rw nth_le_of_fn' _ _ hi_new,
      rw nth_le_of_fn' _ _ _,
      swap, 
      { convert hi_new using 1,
        {symmetry,
        apply congr_arg (λ {b : ℕ}, i - b),
        exact eq_list_lengths_of_modify p2 0,},
        symmetry,
        exact eq_list_lengths_of_modify p2 1,
      },
      by_cases hj : p2.j = 1,
      { set p2l := p2.hl with hp2l,
        set p2n := p2l.n with p2ln,
        by_cases hni : p2n = i - length (G2.f 0),
        { have hG1G2 : game.remove G1 1 ⟨i - length (G1.f 0), begin
            convert hi_new using 1,
            {symmetry,
            apply congr_arg (λ {b : ℕ}, i - b),
            exact eq_list_lengths_of_modify p2 0,},
            symmetry,
            exact eq_list_lengths_of_modify p2 1, 
          end⟩ = game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩,
          { apply game.ext,
            intros a ha,
            cases a with a,
            { unfold game.remove,
              dsimp,
              rw dif_neg, swap, exact dec_trivial,
              rw dif_neg, swap, exact dec_trivial,
              convert (p2.hj 0 _).symm using 1,
              rw hj,
              exact dec_trivial,
            },
            { cases a with a, swap, cases ha, cases ha_a, cases ha_a_a,
              unfold game.remove,
              dsimp,
              rw dif_pos, swap, refl,
              rw dif_pos, swap, refl,
              rw ← eq_list_lengths_of_modify p2 0,
              rw ←hni,
              rw p2ln,
              convert p2l.heq.symm; rw ← hj,
            }
          },
          rw hG1G2,
          convert p2l.bound using 1,
          apply congr_arg,
          dsimp,
          simp only [p2ln.symm, hni, hj],
          simp only [eq_list_lengths_of_modify p2 0],
          ring,
        },
        { -- in this case nth_le (G2.f 0) i _ = nth_le (G1.f 0) i _
          -- and we can use the inductive hypothesis-
          -- should use list.modify_same, but duplicates create
          -- problems (come from nth_le as well)
          
          
          --rw hj at p2l,
          have nth_le_eq : nth_le (G2.f 1) (i - length (G2.f 0)) _ 
          = nth_le (G1.f 1) (i - length (G2.f 0)) _,
          apply list.modify_same _ (i - length (G2.f 0)) _ _ _,
          exact d,
          simp only [hj] at p2l,
          exact p2l,
          convert hni,
          rw eq_comm,
          exact hj,
          rw eq_comm,
          exact hj,
          --library_search
          exact cast_heq
          ((λ (A A_1 : list ℤ) (e_1 : A = A_1) (B B_1 : list ℤ) (e_2 : B = B_1) (d d_1 : ℤ) (e_3 : d = d_1),
              congr (congr (congr_arg list.modify e_1) e_2) e_3)
            (G2.f (p2.j))
            (G2.f 1)
            ((λ (c c_1 : game 2) (e_1 : c = c_1) (a a_1 : fin 2) (e_2 : a = a_1), congr (congr_arg f e_1) e_2) G2 G2
                (eq.refl G2)
                (p2.j)
                1
                hj)
            (G1.f (p2.j))
            (G1.f 1)
            ((λ (c c_1 : game 2) (e_1 : c = c_1) (a a_1 : fin 2) (e_2 : a = a_1), congr (congr_arg f e_1) e_2) G1 G1
                (eq.refl G1)
                (p2.j)
                1
                hj)
            d
            d
            (eq.refl d))
          p2l,--up to here by library_search
          simp only [nth_le_eq],
          
          convert (H (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩) _ (game.remove G1 1 ⟨i - length (G1.f 0), _⟩) 
          (game.remove_of_modify_symm p2 1 ⟨i - length (G2.f 0), hi_new⟩ ⟨i - length (G1.f 0), _⟩ _)) using 1,
          {apply congr_arg,
          dsimp,
          --simp only [p2ln.symm, hni, hj],
          ring,
          sorry,
          },
          { convert hi_new using 1,
            symmetry,
            apply eq_list_lengths_of_modify p2,
          },
          { convert hi_new using 1,
            {symmetry,
            apply congr_arg (λ {b : ℕ}, i - b),
            exact eq_list_lengths_of_modify p2 0,},
            symmetry,
            exact eq_list_lengths_of_modify p2 1,
          },
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
          {apply congr_arg (λ {b : ℕ}, i - b),
           exact eq_list_lengths_of_modify p2 0,
          },
          {exact hi_new},

        },
      },
      { have G1G2_1 : G2.f 1 = G1.f 1,
        rw eq_comm at hj,
        exact p2.hj 1 hj,
        simp only [G1G2_1],
        { convert (H (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩) _ 
        (game.remove G1 1 ⟨i - length (G1.f 0), _⟩) 
        (game.remove_of_modify_symm p2 1 ⟨i - length (G2.f 0), hi_new⟩ ⟨i - length (G1.f 0), _⟩ _)) using 1,
          {apply congr_arg,
          dsimp,
          --simp only [p2ln.symm, hni, hj],
          ring,
          sorry,
          },
          { convert hi_new using 1,
            {symmetry,
            apply congr_arg (λ {b : ℕ}, i - b),
            exact eq_list_lengths_of_modify p2 0,},
            symmetry,
            exact eq_list_lengths_of_modify p2 1,
          },
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
          {apply congr_arg (λ {b : ℕ}, i - b),
           exact eq_list_lengths_of_modify p2 0,
          },

        },

        },
        },
  },
end

/- todo

1) Fill in sorrys (first two shouldn't be hard, third might be more of a challenge, but I am pretty
sure I can do it)
2) Prove that if `h : game.modify G1 G2 d` then int.nat_abs(G1.value - G2.value) <= d by induction on size

-/


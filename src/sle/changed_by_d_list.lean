import data.list.basic tactic.linarith
import tactic.omega tactic.apply

open list

-- changing one element of a list by at most d

structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d)

lemma cons_eq_sing_append {b : list ℤ} (a : ℤ):
(a::b) = [a] ++ b :=
begin 
refl,
end

-- this looks easier
theorem eq_size_of_modify_list (l1 l2 : list ℤ ) (d : ℤ) (h : list.modify l1 l2 d) : l1.length = l2.length :=
begin
  cases h, have P : length(remove_nth l1 h_n) = length(remove_nth l2 h_n), rw h_heq, 
  rw length_remove_nth  at P, rw length_remove_nth  at P,  have Q : ¬ h_n < 0, simp,
  cases l1, dsimp at h_ha, exfalso, finish, cases l2, dsimp at h_hb,
  exfalso, finish, finish, exact h_hb, exact h_ha,
  end

/-
--WRONG
lemma nth_le_rem_nth {A : list ℤ} {n : ℕ } : ∀ (x : ℕ) (h_neq : x ≠ n)
(ha1: x < length A) (ha2: x < length(remove_nth A n)), 
(nth_le A x ha1 = nth_le (remove_nth A n) x ha2):=
begin
intros x hx ha1 ha2, induction A with hb B,  
dsimp at *, exact false.elim ((nat.not_lt_zero x) ha1), 
simp only [cons_eq_sing_append B hb],
rw cons_eq_sing_append B hb at *, 
--rw nth_le_append_right hb ha1 , --dsimp at *,   
--schon wieder dieses Problem 

sorry,
end-/

@[simp] theorem nth_le_reverse' {α : Type*} (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) i h1 = nth_le l (length l - 1 - i) h2 :=
begin
  convert nth_le_reverse l _ _ _,
  rw length_reverse at h1,
  { generalize hL : length l = L,
    rw hL at h1,
    clear hL h2 l α, -- working around bugs in old mathlib
    omega
  },
  { generalize hL : length l = L,
    rw  length_reverse  at *,
    rw hL at *,
    
    clear hL l α,
    omega,



  }
end

lemma nth_le_zero {α : Type*} [inhabited α] (l : list α) (h : _) :
  nth_le l 0 h = head l :=
begin
  cases l with a m,
    exfalso, revert h, exact dec_trivial,
  refl,
end

lemma nth_le_take {α : Type*} (l : list α) (n m : ℕ) (h1) (h2) :
nth_le (take m l) n h1 = nth_le l n h2 :=
begin
  rw length_take at h1,
  rename h1 h3,
  rw lt_min_iff at h3,
  cases h3 with H1 H2,
  revert m n,
  induction l with k hk IH,
  { intros, exfalso, rw length at H2,
    cases H2},
  intros,
  cases m with m',
  { simp only [take_zero],
      cases H1},
  { simp only [take],
    cases n with n',
      refl,
    rw nth_le,
    rw nth_le,
    apply IH,
      apply nat.lt_of_succ_lt_succ, assumption,
    apply nat.lt_of_succ_lt_succ, assumption,
  }
end

-- should probably name it nth_le_eq_head_reverse_take
lemma head_reverse_take {A : list ℤ} {n : ℕ } (h : n < length A):
  head (reverse (take (n + 1) A)) = nth_le A n h :=
begin
  have H1 : 0 < length (reverse (take (n + 1) A)),
   { rw length_reverse,
     rw length_take,
     -- we did this somewhere else
     apply lt_min,
       linarith,
     refine lt_of_le_of_lt _ h,
     linarith,
},
  have H : head (reverse (take (n + 1) A)) = nth_le (reverse (take (n + 1) A)) 0 H1,
    rw nth_le_zero,
  rw H, -- now have nth_le (reverse)
rw nth_le_reverse' _ _ _ _,
  swap,
  { rw length_take,
    rw nat.sub_zero,
    apply buffer.lt_aux_2,
    have H : 0 < (n + 1) := by norm_num,
    apply lt_of_lt_of_le H,
    apply le_min (le_refl _),
    linarith },
  simp only [length_take],
  rw nth_le_take,
    swap,
  { rw nat.sub_zero,
    have H2 : 0 < min (n + 1) (length A),
    { apply lt_min,
      { linarith},
      apply lt_of_le_of_lt _ h,
      linarith,
    },
    rw nat.sub_lt_right_iff_lt_add,
    { apply lt_of_le_of_lt _ (nat.lt_succ_self _),
      apply min_le_right},
    apply le_min,
    {linarith},
    {show 0 < length A,
     apply lt_of_le_of_lt _ h,
     linarith}
  },
  congr',
  rw nat.sub_zero,
  have H3 : n + 1 ≤ length A,
  {linarith},
  rw min_eq_left H3,
  clear h H H1 H3 ,
  omega,

end

lemma drop_zero {α : Type*} {L : list α}: drop 0 L = L := begin refl, end

lemma take_lemma_base_case {A B : list ℤ} {x: ℕ } :
take (nat.succ x) A = take (nat.succ x) B → take x A = take x B :=
begin 
revert x, revert B,
induction A with a An,
intro B, intro x,
cases B with b Bn,
rw take_nil,
rw take_nil,
simp,

intro H,
exfalso,
rw take_nil at H,
rw take_cons at H,
simp at H,
exact H,
intro B, intro x,
cases B with b Bn,
intro H,
exfalso,
rw take_nil at H,
rw take_cons at H,
simp at H,
exact H,
cases x,
intro H,
rw take_zero, rw take_zero,
intro H,
rw take_cons,
rw take_cons,
rw take_cons at H,
rw take_cons at H,
rw cons_eq_sing_append at H,

rw cons_eq_sing_append b at H,

have H_left : [a] = [b] , rw append_inj_right H, 
simp,
have H_right : take (nat.succ x) An = take (nat.succ x) Bn,
rw append_inj_left H, simp,

rw cons_eq_sing_append,
rw cons_eq_sing_append b,
rw H_left,
rw append_left_inj [b],
exact A_ih H_right,


end


lemma take_lemma {A B : list ℤ} {x y : ℕ } (h : y ≤  x):
take x A = take x B → take y A = take y B :=
begin
revert A, revert B,
have P : ∃ (n:ℕ), x = y + n, exact le_iff_exists_add.mp h,
cases P with n Pn, 
have Py : y = x - n,
rw Pn, rw nat.add_sub_cancel,
rw Py,
revert x, revert y, 
induction n with d hd,
repeat {rw nat.add_zero},
simp,
intros y x P Px Py B A H,


cases A with a An,
cases B with b Bn,
refl,
cases y,
rw take_nil, rw ← Py,
rw take_zero, rw ← Py,
exfalso,
rw take_nil at H, rw Px at H,

rw take_cons at H,
simp at H,
exact H,
cases B with b Bn,
cases y,
rw take_nil, rw ← Py,
rw take_zero,
exfalso,
rw take_nil at H, rw Px at H,
rw take_cons at H,
simp at H,
exact H,
cases y, rw ← Py, 
rw take_zero,
rw take_zero,
rw ← Py, 
rw take_cons,
rw take_cons,
rw Px at H,
rw take_cons at H,
rw take_cons at H,

rw cons_eq_sing_append at H,

rw cons_eq_sing_append b at H,

have H_left : [a] = [b] , rw append_inj_right H, 
simp,
have H_right : take (nat.succ y + d) An = take (nat.succ y + d) Bn,
rw append_inj_left H, simp,

rw cons_eq_sing_append,
rw cons_eq_sing_append b,
rw H_left,
rw append_left_inj [b],
rw nat.succ_add at H_right,
have H_new : take (y + d) An = take (y + d) Bn,
exact take_lemma_base_case  H_right,
clear Px Py P H H_left H_right,
have triv1 : y ≤ y + d, simp,
have triv2 : y + d = y + d, refl,
have triv3 : y = y + d - d, simp,
rw triv3,
exact hd triv1 triv2 triv3 H_new,

end

lemma drop_lemma_base_case {A B : list ℤ} {x: ℕ } :
drop x A = drop x B → drop (nat.succ x) A = drop (nat.succ x) B :=
begin 
intro H,
rw nat.succ_eq_add_one, rw add_comm,
rw drop_add, 
rw H,
rw drop_drop,
end

lemma drop_lemma {A B : list ℤ} {x y : ℕ } (h : x ≤ y):
drop x A = drop x B → drop y A = drop y B :=
begin
revert A, revert B,
have P : ∃ (n:ℕ), y = x + n, exact le_iff_exists_add.mp h,
cases P with n Pn, 
have Py : x = y - n,
rw Pn, rw nat.add_sub_cancel,
rw Py,
revert y, revert x, 
induction n with d hd,
repeat {rw nat.add_zero},
simp,
intros x y P Py Px B A H,
rw nat.succ_eq_add_one at Py, rw Py,
rw ← add_assoc,
rw drop_add, rw drop_add (x+d) 1 B,


rw ← Px at H,
have H_new : drop (nat.succ x) A = drop (nat.succ x) B,
exact drop_lemma_base_case H,
rw nat.succ_eq_add_one at H_new,
rw drop_add at H_new, rw drop_add x 1 B at H_new,
have triv1 : x ≤ x + d, simp,
have triv2 : x + d = x + d, refl,
have triv3 : x = x + d - d, simp,
rw triv3 at H_new,

exact hd triv1 triv2 triv3 H_new,

end




lemma tail_drop {A:list ℤ} {m : ℕ} :
tail (drop m A) = drop (nat.succ m) A :=
begin
rw ← drop_one,
rw drop_drop, 
rw add_comm,
end 

-- lemma head_reverse (α : Type*) [inhabited α] (L : list α) :
--   head (reverse L) = ilast L :=
-- begin
--   sorry -- may not need this!
-- end

lemma head_drop (α : Type*) [inhabited α] (L : list α) (m : ℕ) (hm : m < L.length):
  head (drop m L) = nth_le L m hm :=
begin
  revert L,
  induction m with d hd,
  { -- base case m=0
    intros L hL,
    rw drop_zero,
    rw nth_le_zero,
  },
  intros L hm,
  induction L with a M H,
    cases hm,
  apply hd,
end

lemma take_drop_head_eq {A:list ℤ} {m : ℕ} (h1: 1 ≤ m) (h2: m + 1 ≤ length A):
head (reverse (take (m+1) A)) = head (tail (drop (m-1) A)):=
begin
  rw tail_drop,
  rw head_reverse_take h2,
  rw [nat.succ_eq_add_one, nat.sub_add_cancel h1],
  rw head_drop,
end



lemma take_drop_head_eq' {A:list ℤ} {d : ℕ} (h2: d + 2 ≤ length A):
head (reverse (take (d+2) A)) = head (tail (drop d A)):=
by rw [tail_drop, head_reverse_take h2, head_drop]




theorem list.modify_same {A : list ℤ} {B : list ℤ} {d : ℤ}
  (h : list.modify A B d) (m : ℕ) (hmA : m < A.length) (hmB : m < B.length)
  (hmn : h.n ≠ m) : A.nth_le m hmA = B.nth_le m hmB :=
begin
  have H : length A = length B, exact eq_size_of_modify_list A B d h,
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



def list.modify.symm (A B : list ℤ) (d : ℤ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  bound := by rw [←neg_sub, abs_neg]; exact m.bound
}

structure game :=
(C : list ℤ) (L : list ℤ)

namespace game
--extensionaliti changes in new mathlib
@[ext] def ext (G1 G2 : game) : G1 = G2 ↔ G1.C = G2.C ∧ G1.L = G2.L :=
by cases G1; cases G2; simp

-- for use later, in the MITM proof
inductive modify (G1 G2 : game) (d : ℤ)
| modifyc : list.modify G1.C G2.C d → (G1.L = G2.L) → modify
| modifyl : list.modify G1.L G2.L d → (G1.C = G2.C) → modify

def size (G : game) : ℕ := list.length G.C + list.length G.L

def zero : game := ⟨[], []⟩

lemma size_zero : zero.size = 0 := rfl

lemma eq_zero_of_size_zero {G : game} : G.size = 0 → G = zero :=
begin
  intro h,
  replace h := nat.eq_zero_of_add_eq_zero h,
  cases h with h1 h2,
  rw length_eq_zero at h1 h2,
  cases G, cases h1, cases h2, refl,
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

def game.rec_on_size' (C : game → Sort*) :
(∀ G : game, G.size = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game, G.size = m → C G := λ z ih n, nat.rec z ih n

universe u
--@[elab_as_eliminator]
def game.rec_on_size {C : game → Sort u} :
C game.zero → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ G : game, C G :=
λ z ih G, @game.rec_on_size' C (λ H hH, (by rwa eq_zero_of_size_zero hH : C H)) ih (G.size) _ rfl

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



/-- Man in the middle for all-chain or all-loop situations -/
theorem MITM_baby (tf : ℤ) (L1 L2 : list ℤ) (d : ℤ) (h : list.modify L1 L2 d)
  (n : ℕ) (hL1 : L1.length = n) (hL2 : L2.length = n) (i : fin n) :
  abs (list.value_i tf n L1 i hL1 - list.value_i tf n L2 i hL2) ≤ d :=
begin
  revert L1 L2,
  induction n with d hd,
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
    -- you will need a function
    -- Π (h : list.modify A B d), Π (m : ℕ), m ≠ h.n → m < A.length →
    --  list.modify (A - m) (B - m) d 
    -- where A - m is A.remove_nth m 
    --have P : list.modify (L1.remove_nth m) (L2.remove_nth m) d, sorry,
    
    

    
    sorry ,
    }
end

  


def game.value : game → ℤ := @game.rec_on_size (λ G, ℤ) (0 : ℤ) $ λ n hn G hG,
  list.min 
    ((list.of_fn $ λ (i : fin G.C.length),
    G.C.nth_le i.val i.is_lt - 2 + abs (2 - hn {C := G.C.remove_nth i.val, L := G.L} begin
      unfold size, unfold size at hG, cases G,  rw remove_nth_eq_nth_tail,
      rw modify_nth_tail_eq_take_drop, show length (take (i.val) G_C ++ tail (drop (i.val) G_C)) + length G_L = n,
      rw list.length_append, rw length_take, rw length_tail, rw length_drop, 
      cases i with hi hj, show min hi (length G_C) + (length G_C - hi - 1) + length G_L = n,
      rw min_eq_left(le_of_lt hj), dsimp at hj, dsimp at hG, generalize hc:length G_C = c, rw hc at *,
       generalize hl:length G_L = l, rw hl at *,clear hc, clear G_C,clear hl G_L hn ,  omega, 
       refl, 
      
    end)) ++ (list.of_fn $ λ (i : fin G.L.length),
    G.L.nth_le i.val i.is_lt - 4 + abs (4 - hn {C := G.C, L := G.L.remove_nth i.val} begin
     unfold size, unfold size at hG, cases G,  rw remove_nth_eq_nth_tail,
      rw modify_nth_tail_eq_take_drop, show length G_C + length (take (i.val) G_L ++ tail (drop (i.val) G_L)) = n,
      rw list.length_append, rw length_take, rw length_tail, rw length_drop, 
      cases i with hi hj, show length G_C + (min hi (length G_L) + (length G_L - hi - 1)) = n, 
      rw min_eq_left(le_of_lt hj), dsimp at hj, dsimp at hG, generalize hc:length G_C = c, rw hc at *,
       generalize hl:length G_L = l, rw hl at *,clear hc, clear G_C,clear hl G_L hn ,  omega, refl, 
    end))) 
    begin
      apply ne_nil_of_length_pos, suffices : 0 < length (G.C) + length (G.L),simpa using this, unfold size at hG, rw hG, simp,
    end.




-- this looks easier
theorem eq_size_of_modify {G1 G2 : game} {d : ℤ} (h : game.modify G1 G2 d) : G1.size = G2.size :=
begin
  cases h, 
  unfold size, rw h_a_1, rw @add_right_cancel_iff _ _ (G2.L).length,  
  exact eq_size_of_modify_list G1.C G2.C d h_a,
  unfold size, rw h_a_1, rw @add_left_cancel_iff _ _ (G2.C).length,  
  exact eq_size_of_modify_list G1.L G2.L d h_a,
end





-- this is the big challenge
theorem MITM (G1 G2 : game) (d : ℤ) (h1 : game.modify G1 G2 d) (h2 : 0 ≤ d):
 abs(G1.value - G2.value) ≤ d :=
begin
  revert G1,
  revert G2,
  apply @game.rec_on_size (λ G2, ∀ G1, modify G1 G2 d → 
  abs (game.value G1 - game.value G2) ≤ d),
  -- this might be tricky!
  { intros G h1, have h3 : G.size = zero.size := eq_size_of_modify h1,
  rw size_zero at h3, have H := eq_zero_of_size_zero h3, 
  rw H, show  0 ≤ d, exact h2},
  { intros n H G1 p G2 p2,
    have hs := eq_size_of_modify p2,
    rw p at hs,
    unfold game.value,
    unfold game.rec_on_size,
    unfold game.rec_on_size',
--    dsimp,
    simp only [hs, p, (nat.succ_eq_add_one n).symm],
    apply list.min_change,
    { rw [length_append, length_of_fn, length_of_fn, length_append, length_of_fn, length_of_fn],
      show G2.size = G1.size,
      rw [p, hs]},
    intros i hiL hiM,
    rw [length_append, length_of_fn, length_of_fn] at hiL hiM,
    dsimp, 
    sorry
  },
end
/- todo

1) Fill in sorrys (first two shouldn't be hard, third might be more of a challenge, but I am pretty
sure I can do it)
2) Prove that if `h : game.modify G1 G2 d` then int.nat_abs(G1.value - G2.value) <= d by induction on size

-/


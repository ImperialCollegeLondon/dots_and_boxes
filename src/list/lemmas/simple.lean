import data.list.basic tactic.linarith
import tactic.omega tactic.apply

open list


/- cons -/

/-- (a::L) is the same as [a] ++ L-/
lemma cons_eq_sing_append {α : Type*} {L : list α } (a : α ):
(a::L) = [a] ++ L := by refl


/- bind -/

theorem list.bind_fin2 {α : Type*} (f : fin 2 → list α) : 
  list.bind [0, 1] f = f 0 ++ f 1 :=
begin
  show f 0 ++ (f 1 ++ nil) = f 0 ++ f 1,
  rw append_nil,
end

/- tail -/

lemma tail_drop (α : Type*) {A:list α} {m : ℕ} :
tail (drop m A) = drop (nat.succ m) A :=
by rw [← drop_one, drop_drop, add_comm]
/-
begin
rw ← drop_one,
rw drop_drop, 
rw add_comm,
end 
-/


/- drop -/

/-- dropping no elements from a list gives the list-/
lemma drop_zero {α : Type*} {L : list α}: drop 0 L = L := by refl


lemma drop_append_of_length_le {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
  length l₁ ≤ n → drop n (l₁ ++ l₂) = drop (n - l₁.length) l₂ :=
begin
  revert n,
  induction l₁ with c L H,
  { intros n h,
    rw nil_append,
    rw length,
    rw nat.sub_zero},
  { intros n h,
    rw length_cons,
    rw cons_append,
    cases n,
    exfalso,
    rw length_cons at h,
    exact nat.not_succ_le_zero (length L) h,
    rw drop,
    rw nat.succ_eq_add_one,
    rw [length_cons, nat.succ_eq_add_one] at h,
    rw ← nat.sub_le_right_iff_le_add at h,
    rw nat.add_sub_cancel (length L) 1 at h,
    rw H h,
    rw nat.succ_sub_succ n (length L)}  
end 


lemma drop_append {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
  drop n (l₁ ++ l₂) = if n ≤ l₁.length then drop n l₁ ++ l₂ else drop (n - l₁.length) l₂ :=
begin
  split_ifs,
    exact drop_append_of_le_length h,
  apply drop_append_of_length_le,
  linarith,
end


/- take -/

lemma take_append_of_length_le {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
 length l₁ ≤ n →
  take n (l₁ ++ l₂) = l₁ ++ take (n - l₁.length) l₂ :=
begin
  intro h,
  revert n,
  induction l₁ with c L H,
  { intros, 
    rw nil_append,
    rw nil_append,
    refl,
  },
  intro n,
  intro h,
  cases n with m,
    cases h, -- kill n = 0 case
  rw cons_append,
  rw take_cons,
  rw cons_append,
  congr',
  rw H,
  { congr' 2,
    rw length_cons,
    generalize : length L = d,
    simp,
  },
  rw length_cons at h,
  revert h,
  exact nat.pred_le_iff.mpr
end

lemma take_append {α : Type*} {l₁ l₂ : list α} {n : ℕ} :

  take n (l₁ ++ l₂) = 
  if ( n ≤ length l₁) then take n l₁ else l₁ ++ take (n - l₁.length) l₂ :=
begin
  split_ifs,
    exact take_append_of_le_length h,
  apply take_append_of_length_le,
  linarith,
end


/- remove_nth -/

lemma remove_nth_zero {α : Type*} (L : list α) : remove_nth L 0 = tail L :=
by cases L; refl

lemma remove_nth_succ {α : Type*}  [inhabited α]{n : ℕ} ( L : list α) ( l : α ): 
remove_nth (l::L) (nat.succ n) = l :: remove_nth L n:=  
begin

--tactic state :  α : Type u_1,
--                _inst_1 : inhabited α,
--                n : ℕ,
--                L : list α,
--                l : α
--                ⊢ remove_nth (l :: L) (nat.succ n) = l :: remove_nth L n

cases L with a L1, 

--tactic state : 2 goals
--               case list.nil
--               α : Type u_1,
--               _inst_1 : inhabited α,
--               n : ℕ,
--               l : α
--               ⊢ remove_nth [l] (nat.succ n) = l :: remove_nth nil n

--               case list.cons
--               α : Type u_1,
--               _inst_1 : inhabited α,
--               n : ℕ,
--               l a : α,
--               L1 : list α
--               ⊢ remove_nth (l :: a :: L1) (nat.succ n) = 
--                 l :: remove_nth (a :: L1) n
refl,
refl,
end

lemma remove_nth_large_n {α : Type*}  [inhabited α]{n : ℕ} (L : list α) (h : length L ≤ n): 
remove_nth L n = L :=
begin
revert L,
induction n with d hd,
intros L h,
have p : L = nil,
rw ←  length_eq_zero, 
exact le_zero_iff_eq.mp h,
rw p, 
refl,
intro L,
cases L with l Lt,
intro h, 
refl,
intro h,
rw remove_nth_succ Lt l,
rw length_cons at h,
rw hd Lt (nat.le_of_succ_le_succ h),
end


/- nth_le -/

/--the zeroth element of the list is its head-/
lemma nth_le_zero {α : Type*} [inhabited α] (l : list α) (h : _) :
  nth_le l 0 h = head l :=
  --by cases l with a m;revert h; by exact dec_trivial; refl

begin
  cases l with a m,
    exfalso,
    revert h, 
    exact dec_trivial,
  refl,
end


/-- the ith element of the reverted list is the (length l - 1 - i)th element of the list-/
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

/--the nth element of the first m elements is the nth element if n < m-/
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


@[simp] theorem nth_le_of_fn' {α : Type*} {n : ℕ} (f : fin n → α)
  (i : ℕ) (hi : i < n) :
  nth_le (of_fn f) i ((length_of_fn f).symm ▸ hi) = f ⟨i, hi⟩ :=
option.some.inj $ by rw [← nth_le_nth];
  simp only [list.nth_of_fn, of_fn_nth_val, fin.eta, dif_pos hi]


/- head -/

/--if two lists are equal, their heads are equal-/
lemma head_eq_of_list_eq {α : Type*} [inhabited α] {L1 L2 : list α}:
L1 = L2 → list.head L1 = list.head L2:= 
begin
--Tactic state: α : Type u_1,
--              _inst_1 : inhabited α,
--              L1 L2 : list α
--              ⊢ L1 = L2 → head L1 = head L2
intro h,
--Tactic state: α : Type u_1,
--              _inst_1 : inhabited α,
--              L1 L2 : list α
--              h : L1 = L2
--              ⊢ head L1 = head L2
rw h,
--Tactic state: goals accomplished
end


/--The head of a list with its first m element dropped is
   its (m+1)th element-/
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
  exact hd M _,
end


/- sum -/

theorem sum_list2 (α : Type*) [add_monoid α] (x y : α) : list.sum [x, y] = x + y :=
begin
  rw list.sum_cons,
  rw list.sum_cons,
  rw list.sum_nil,
  rw add_zero,
end
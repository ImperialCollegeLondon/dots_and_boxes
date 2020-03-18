import data.list.basic tactic.linarith
import tactic.omega tactic.apply

open list

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
/-- (a::L) is the same as [a] ++ L-/
lemma cons_eq_sing_append {α : Type*} {L : list α } (a : α ):
(a::L) = [a] ++ L := by refl



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

-- should probably name it nth_le_eq_head_reverse_take
/--If you take the head of the first n+1 elements in reverse order you get the nth element-/
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

/-- dropping no elements from a list gives the list-/
lemma drop_zero {α : Type*} {L : list α}: drop 0 L = L := by refl

/--If the first x+1 elements of two lists are the same, so are the first x-/
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

/--If the first x elements of two lists are the same, so are the first y if y ≤ x-/
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

/--If dropping the first x elements of two lists gives the same list, so does dropping the first x + 1-/
lemma drop_lemma_base_case {A B : list ℤ} {x: ℕ } :
drop x A = drop x B → drop (nat.succ x) A = drop (nat.succ x) B :=
begin 
intro H,
rw nat.succ_eq_add_one, rw add_comm,
rw drop_add, 
rw H,
rw drop_drop,
end

/--If dropping the first x elements of two lists gives the same list, so does dropping the first y if y ≥ x-/
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
by rw [
       tail_drop, head_reverse_take h2, nat.succ_eq_add_one, 
       nat.sub_add_cancel h1, head_drop
       ]
/-
begin
  rw tail_drop,
  rw head_reverse_take h2,
  rw [nat.succ_eq_add_one, nat.sub_add_cancel h1],
  rw head_drop,
end
-/


lemma take_drop_head_eq' {A:list ℤ} {d : ℕ} (h2: d + 2 ≤ length A):
head (reverse (take (d+2) A)) = head (tail (drop d A)):=
by rw [tail_drop, head_reverse_take h2, head_drop]


lemma remove_nth_eq_take_add_drop (a : ℕ) (L : list ℤ) :
  remove_nth L a = take a L ++ drop (a + 1) L :=
begin
  rw remove_nth_eq_nth_tail,
  rw modify_nth_tail_eq_take_drop,
  rw tail_drop,
  refl,
end

--#check @take_append_of_le_length
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

lemma remove_nth_zero {α : Type*} (L : list α) : remove_nth L 0 = tail L :=
by cases L; refl

lemma remove_nth_succ {α : Type*}  [inhabited α]{n : ℕ} ( L : list α) ( l : α ): remove_nth (l::L) (nat.succ n) = 
l :: remove_nth L n:=  
begin
cases L, refl,refl,
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
rw p, refl,
intro L,
cases L with l Lt,
intro h, refl,
intro h,
rw remove_nth_succ Lt l,
rw length_cons at h,
rw hd Lt (nat.le_of_succ_le_succ h),
end

/--changing the order of element removel of a list of naturals-/
lemma remove_nth_remove_nth {a b : ℕ } (L : list ℤ)(Ha : a ≤ length L)(Hb : b + 1 ≤ length L):
remove_nth (remove_nth L a) b = if a < (b + 1) then remove_nth (remove_nth L (b+1)) a 
else remove_nth (remove_nth L b) (a-1):=
begin
  cases a with a,
  { rw [if_pos (nat.zero_lt_succ _), remove_nth_zero, remove_nth_zero],
    clear Ha Hb,
    revert b,
    induction L with c L H,
      intros, refl,
    intros,
    refl,
  },
  split_ifs,
  { rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw drop_append,
    split_ifs,
      rw [length_take, lt_min_iff] at h_1, cases h_1, linarith,
    clear h_1,
    rw @take_append _ _ _ (a + 1),
    split_ifs,
      swap,
      { push_neg at h_1,
        rw [length_take] at h_1,
        exfalso,
        rw min_eq_left at h_1,
          change a + 1 < _ at h,
          linarith,
        assumption,
      },
    rw take_append,
    rw drop_append,
    rw ←drop_take,
    rw length_take,
    rw length_take,
    rw min_eq_left Hb,
    rw min_eq_left Ha,
    rw nat.succ_eq_add_one at *,
    clear h_1,
    rw if_pos (show a+1+1≤b+1, from h),
    split_ifs,
    { rw le_iff_eq_or_lt at h_1,
      cases h_1,
        swap, exfalso, linarith,
      rw ←h_1,
      rw take_take,
      rw min_self,
      rw take_take,
      rw min_eq_left, swap, simp only [zero_le, le_add_iff_nonneg_right],
      congr',
      rw drop_drop,
      -- need drop n (take n L) = nil.
      convert (nil_append _).symm using 2,
        convert drop_all _,
        rw length_take,
        rw min_eq_left,
        assumption,
      congr' 1,
      clear Hb Ha, omega,
    },
    { push_neg at h_1,
      rw drop_drop,
      rw take_take,
      rw min_eq_left,
      have p1 : b + 1 - (a + 1) + (a + 1 + 1) = b + 1 + 1,
      clear Hb Ha,
      omega,
      rw p1,
      clear p1,
      have p2 : a + 1 + 1 + (b - (a + 1)) = b + 1,
      clear Hb Ha,
      omega,
      rw p2,
      clear p2,
      simp,
      linarith,
      }

  },
  { rw nat.succ_eq_add_one at *,
    rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw remove_nth_eq_take_add_drop,
    rw take_append,
    split_ifs,
      swap,
      exfalso,
      push_neg at h_1,
      rw length_take at h_1,
      rw min_eq_left at h_1,
      linarith,
      exact Ha,
    rw drop_append,
    push_neg at h,
    rw length_take,
    rw min_eq_left,
    rw if_pos,
    rw drop_append,
    split_ifs,
    rw length_take at h_2,
    rw min_eq_left at h_2,
    exfalso,
    clear Ha Hb h_1,
    omega, 
    apply le_trans,
    swap 3, exact (b+1),
    simp,
    exact Hb,
    rw take_append,
    rw length_take,
    rw min_eq_left,
    split_ifs,
    push_neg at h_2,
    have eq: a + 1 - 1 = b,
      rw length_take at h_2,
      rw min_eq_left at h_2,
      exact le_antisymm h_3 h_2,
    apply le_trans,
    swap 3, exact (b+1),
    simp,
    exact Hb,
    rw nat.add_sub_cancel at eq,
    rw eq,
    rw nat.add_sub_cancel,
    rw take_take,
    rw drop_drop,
    rw ← nil_append (drop (b + 1 - b + (b + 1)) L),
    rw take_take,
    clear eq,
    rw min_eq_left,
    rw min_eq_left,
    simp only [add_zero, nat.add_sub_cancel_left, add_comm, le_add_iff_nonneg_right],
    rw append_left_inj (take b L),
    rw append_right_inj (drop (1 + (b + 1)) L),
    convert drop_all _,
    rw length_take,
    rw min_eq_left,
    exact Hb,
    exact le_refl b,
    simp,
    clear h_2,
    rw take_take,
    rw drop_drop,
    rw length_take at *,
    rw min_eq_left at *,
    rw ← drop_take,
    have p1 : b + 1 + (a + 1 - 1 - b) = a + 1,
      clear Hb Ha,
      omega,
    rw p1,
    clear p1,
    have p2 : a + 1 - 1 + 1 - b + (b + 1) = a + 1 + 1,
      clear Hb Ha,
      omega,
    rw p2,
    clear p2,
    simp,
    exact h_1,
    exact Ha,
    apply le_trans,
    swap 3, exact (b+1),
    simp,
    exact Hb,
    exact h,
    exact Ha,
},
end


lemma remove_nth_eq_remove_nth_to_length_eq {α : Type*} {A B : list α}:
∀ (n : ℕ) (hA : n < length A)(hB : n < length B), remove_nth A n = remove_nth B n → length A = length B:=
begin
intros n hA hB h,
have p : length (remove_nth A n) = length (remove_nth B n), rw h,
rw length_remove_nth at p,
rw length_remove_nth at p,
have pa : 1 ≤ length A := by exact nat.one_le_of_lt hA, 
have pb : 1 ≤ length B := by exact nat.one_le_of_lt hB, 
exact nat.pred_inj pa pb p,
exact hB,
exact hA,
end

/--if two lists are equal, their heads are equal-/
lemma head_eq_of_list_eq {α : Type*} [inhabited α] {L1 L2 : list α}:
L1 = L2 → list.head L1 = list.head L2:= by intro h; rw h
--begin
--intro h,
--rw h,
--end

/--the nth element of a list with an element removed is the bth or (b+1)th 
element of the full list, depending on which element was removed-/
lemma nth_le_remove_nth {a b : ℕ } (L : list ℤ) (h:b < length (remove_nth L a)) (h1 h2):
nth_le (remove_nth L a) b h = 
if a ≤ b then nth_le L (b+1) h1
else nth_le L b h2:=
begin
split_ifs,
rw ← head_drop,
rw ← head_drop,
rw remove_nth_eq_take_add_drop,
rw drop_append,
split_ifs,
  rw length_take at h_2,
  rw min_eq_left at h_2,
  have p1: a=b:= by exact le_antisymm h_1 h_2,
  rw p1,
  apply head_eq_of_list_eq,
  have p2 : drop b (take b L) = nil,
  convert drop_all _,
  rw length_take,
  rw min_eq_left,
  exact (le_of_lt h2),
  rw p2,
  rw nil_append,
  exact le_trans h_1 (le_of_lt h2),

  rw ← drop_add,
  rw length_take,
  rw min_eq_left,
  show head (drop (b - a + a + 1) L) = head (drop (b + 1) L),
  rw nat.sub_add_cancel h_1,
  exact le_trans h_1 (le_of_lt h2),
  
rw ← head_drop,
rw ← head_drop,
push_neg at h_1,
rw remove_nth_eq_take_add_drop,
rw drop_append,
rw if_pos,
rw head_append,
rw ← take_append_drop a L,
rw drop_append,
rw take_append_drop a L,
rw if_pos,
rw head_append,
swap 3,


apply ne_nil_of_length_eq_succ,
swap, exact min a (length L) - b -1,
rw length_drop,
rw length_take,
rw nat.succ_eq_add_one,
rw nat.sub_add_cancel,
show 1 ≤ (min a (length L)) - b,
have p : 1 + b ≤ min a (length L),
apply le_min,
rw add_comm,
--not exactly sure why this works here, does not work below
exact h_1,
rw add_comm,
exact (le_of_lt h1),
exact nat.le_sub_right_of_add_le p,


apply ne_nil_of_length_eq_succ,
swap, exact min a (length L) - b -1,
rw length_drop,
rw length_take,
rw nat.succ_eq_add_one,
rw nat.sub_add_cancel,
show 1 ≤ (min a (length L)) - b,
have p : 1 + b ≤ min a (length L),
apply le_min,
rw add_comm,
--not exactly sure why this works here, does not work below
exact h_1,
rw add_comm,
exact h2,
exact nat.le_sub_right_of_add_le p,

rw length_take,
apply le_min,
exact (le_of_lt h_1),
exact (le_of_lt h2),

rw length_take,
apply le_min,
exact (le_of_lt h_1),
exact (le_of_lt h2),
end

/--if ∃ an element strictly between a and the sucessor of c in ℕ, then a is smaller than c -/
lemma lt_trans_of_succ {a b c : ℕ}: a < b → b < nat.succ c → a < c :=
begin
intros h1 h2,
rw nat.lt_succ_iff at h2,
exact lt_of_lt_of_le h1 h2,
end

@[simp] theorem nth_le_of_fn' {α : Type*} {n : ℕ} (f : fin n → α)
  (i : ℕ) (hi : i < n) :
  nth_le (of_fn f) i ((length_of_fn f).symm ▸ hi) = f ⟨i, hi⟩ :=
option.some.inj $ by rw [← nth_le_nth];
  simp only [list.nth_of_fn, of_fn_nth_val, fin.eta, dif_pos hi]


lemma abs_le_nonneg {a b : ℤ } : abs(a) ≤ b → 0 ≤ b:=
begin 
have h : 0 ≤ abs(a),
 show abs(a) ≥ 0,
 exact abs_nonneg a,
 intro x,
 exact le_trans h x,
 end
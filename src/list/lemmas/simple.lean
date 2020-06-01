import data.list.basic tactic.linarith
import tactic.omega tactic.apply

open list


/- cons -/

/-- (a::L) is the same as [a] ++ L-/
lemma cons_eq_sing_append {α : Type*} {L : list α } (a : α ):
(a::L) = [a] ++ L := by refl -- true by definition of append


/- bind -/

/--list.bind of two lists is the second appended to the first-/
theorem list.bind_fin2 {α : Type*} (f : fin 2 → list α) : 
  list.bind [0, 1] f = f 0 ++ f 1 :=
begin
  show f 0 ++ (f 1 ++ nil) = f 0 ++ f 1, -- by definition of list.bind
  rw append_nil,
end

/- tail -/

/--the tail of a list with the first m elements dropped is that
list with the first m+1 elements dropped-/
lemma tail_drop (α : Type*) {A:list α} {m : ℕ} :
tail (drop m A) = drop (nat.succ m) A :=
by rw [← drop_one, drop_drop, add_comm]
/-
begin
rw ← drop_one, -- drop 1 L = tail L (here L is drop m A)
rw drop_drop,  -- drop 1 (drop m) A = drop (1 + m) A
rw add_comm,   -- commutativity of + (nat.succ n is defined as n + 1)
end 
-/


/- drop -/

/-- dropping no elements from a list gives the list-/
lemma drop_zero {α : Type*} {L : list α}: drop 0 L = L := by refl --by def of drop


/--If one drops the first n elements of two lists appended to each other and
   the fist list has length l no longer than n, then this is the same as 
   dropping the first n-l elements from the second list-/
lemma drop_append_of_length_le {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
  length l₁ ≤ n → drop n (l₁ ++ l₂) = drop (n - l₁.length) l₂ :=
begin
  revert n, -- revert n so the inductive hyothesis holds for any value of n
  induction l₁ with c L H,
  -- base case: l₁ = nil 
  { intros n h,
    rw nil_append, -- nil ++ l₂ = l₂
    rw length, -- length nil = nil
    rw nat.sub_zero}, -- n-0 = n
  -- inductive step: l_1 = (c :: L), c of type α and L of type list α   
  { intros n h,
    rw length_cons, -- length (c :: L) = length L + 1
    rw cons_append, -- (c :: L) ++ l₂ = (c :: (L ++ l₂))
    cases n,
      -- n = 0,  contradicts length (c :: L) ≤ n (hypothesis h)
      exfalso,
      rw length_cons at h,
      exact nat.not_succ_le_zero (length L) h,
    -- nat.succ n 
    rw drop, -- drop (nat.succ n) (c :: (L ++ l₂)) = drop n (L ++ l₂) by def of drop
    rw nat.succ_eq_add_one,
    rw [length_cons, nat.succ_eq_add_one] at h, 
    rw ← nat.sub_le_right_iff_le_add at h, -- (length L + 1) - 1 ≤ n ↔ (length L + 1) ≤ n + 1
    rw nat.add_sub_cancel (length L) 1 at h,
    rw H h, -- use inductive hypothesis
    rw nat.succ_sub_succ n (length L)} /- nat.succ n - nat.succ (length L) = n - (length L)
                                          nat.succ x defined as x + 1 -/
end 


/--summary of drop_append_of_le_length and drop_append_of_length_le-/
lemma drop_append {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
  drop n (l₁ ++ l₂) = if n ≤ l₁.length then drop n l₁ ++ l₂ else drop (n - l₁.length) l₂ :=
begin
  split_ifs with ite, -- split if-then-else-condition into cases true or not)
    /- if-case (named ite) : n ≤ length l₁-/
    exact drop_append_of_le_length ite, -- existing lemma in mathlib
  /- else-case (named ite) : ¬ (n ≤ length l₁)-/
  apply drop_append_of_length_le, -- lemma above
  --goal : length l₁ ≤ n    necessary hypothesis for drop_append_of_length_le
  linarith, -- lean can do this much by itself
end


/- take -/

/--If one takes the first n elements of two lists appended to each other and
   the fist list has length l no longer than n, then this is the same as 
   taking all of the first list and appending the first n-l elements from 
   the second list-/
lemma take_append_of_length_le {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
 length l₁ ≤ n →
  take n (l₁ ++ l₂) = l₁ ++ take (n - l₁.length) l₂ :=
begin
  revert n, -- revert n so the inductive hyothesis holds for any value of n
  induction l₁ with c L H,
  -- base case: l₁ = nil
  { intros n h, 
    rw nil_append, -- nil ++ l₂ = l₂
    rw nil_append, -- nil ++ take (n - length nil) l₂ = take (n - length nil) l₂
    refl, -- n - length nil = n - 0 = n
  },
  -- inductive step: l₁ = (c :: L), with c of type α and L of type list α 
  intros n h,
  cases n with m,
    cases h, -- kill n = 0 case (h is ength (c :: L) ≤ 0)
  -- nat.succ n
  rw cons_append, -- ((c :: L) ++ l₂) = (c :: (L ++ l₂))
  rw take_cons, -- take (nat.succ m) (c :: (L ++ l₂)) =  c :: take m (L ++ l₂)
  rw cons_append, /- c :: L ++ take (nat.succ m - length (c :: L)) l₂ = 
                     c :: (L ++ take (nat.succ m - length (c :: L)) l₂)-/
  congr', -- eliminates the c at the start on both sides
  rw H, -- use inductive hypothesis
  { congr' 2, -- focused goal becomes : m - length L = nat.succ m - length (c :: L)
    rw length_cons, -- length (c :: L) = ength L + 1
    generalize : length L = d, -- replaces length L by d
    simp, -- Lean can solve the goal by itself now
  },
  -- necessary hypothesis for inductive hypothesis: length L ≤ m
  rw length_cons at h,
  revert h,
  exact nat.pred_le_iff.mpr -- solves goal : length L + 1 ≤ nat.succ m → length L ≤ m
end


/--summary of  take_append_of_le_length and take_append_of_length_le-/
lemma take_append {α : Type*} {l₁ l₂ : list α} {n : ℕ} :
  take n (l₁ ++ l₂) = 
  if ( n ≤ length l₁) then take n l₁ else l₁ ++ take (n - l₁.length) l₂ :=
begin
    split_ifs with ite, -- split if-then-else-condition into cases true or not)
    /- if-case (named ite) : n ≤ length l₁-/
    exact take_append_of_le_length ite, -- existing lemma in mathlib
  /- else-case (named ite) : ¬ (n ≤ length l₁)-/
  apply take_append_of_length_le, -- lemma above
  --goal : length l₁ ≤ n    necessary hypothesis for drop_append_of_length_le
  linarith, -- lean can do this much by itself
end


/- remove_nth -/

/--removing only the 0th element gives the tail-/
lemma remove_nth_zero {α : Type*} (L : list α) : remove_nth L 0 = tail L :=
--proof in term mode
by cases L; refl

/--removing the (n+1)th element gives the 'tail' of the list with 
   the nth element removed, concatenated to the first element   -/
lemma remove_nth_succ {α : Type*}  {n : ℕ} ( L : list α) ( l : α ): 
remove_nth (l::L) (nat.succ n) = l :: remove_nth L n:=  
begin
cases L with a L1, 
-- L = nil
refl, -- by def of remove_nth
-- L = (a :: L1)
refl, -- by def of remove_nth
end


/--If we try to remove an entry outside of the list, we get the unchanged list-/
lemma remove_nth_large_n {α : Type*} {n : ℕ} (L : list α) (h : length L ≤ n): 
remove_nth L n = L :=
begin
revert L, -- so the inductive hypothesis holds for any list of length ≤ n
induction n with d hd,
-- base case : n = 0
  {intros L h,
  have p : L = nil, -- because of h, as the only list of length 0 is nil
    {rw ←  length_eq_zero, -- length L = 0 ↔ L = nil
    exact le_zero_iff_eq.mp h},
  rw p, 
  refl}, -- by def of remove_nth
-- inductive step : n = nat.succ d
{intros L h,
cases L with l Lt,
  -- L = nil
  {refl}, -- by def of remove_nth
-- L = (l :: Lt), with l of type α and Lt of type list α
{rw remove_nth_succ Lt l, 
rw length_cons at h,
rw hd Lt (nat.le_of_succ_le_succ h)},}, -- use inductive hypothesis
end


/- nth_le -/

/--the zeroth element of the list is its head-/
lemma nth_le_zero {α : Type*} [inhabited α] (l : list α) (h : _) :
  nth_le l 0 h = head l :=
begin
  cases l with m M,
    -- l = nil     contradicts (h : 0 < length l)
    {exfalso,
    revert h, 
    exact dec_trivial},
  -- L = (m :: M), with m of type α and M of type list α  
  refl, -- by def of nth_le
end


/-- the ith element of the reverted list is the (length l - 1 - i)th element of the list-/
@[simp] theorem nth_le_reverse' {α : Type*} (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) i h1 = nth_le l (length l - 1 - i) h2 :=
begin
  /- this lemma is just a slightly different version of nth_le_reverse, which says
     for any ist l , natural number i
     nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2
     where h1,h2 are the respective proofs that the lists have an element 
     of the index asked for-/

  convert nth_le_reverse l _ _ _, -- convert the goal using nth_le_reverse

  -- first goal : i = length l - 1 - (length l - 1 - i)
  rw length_reverse at h1, -- length (reverse l) = length l
  { generalize hL : length l = x, -- create hyothesis length l = x for some x ∈ ℕ 
    rw hL at h1,
    clear hL h2 l α, -- working around bugs in old mathlib
    omega -- let Lean solve this by itself (using linear integer and natural number arithmetic)
  },

  /- other goal : length l - 1 - (length l - 1 - i) < length (reverse l)  
     (needed as argument for nth_le) -/
  { generalize hL : length l = x, -- create hyothesis length l = x for some x ∈ ℕ  
    rw  length_reverse  at *, -- rewrite using length_reverse everywhere
    rw hL at *,

    -- now the goal is equivalent to h1 after getting rid of cancelling terms
    
    clear hL l α, -- working around bugs in old mathlib
    omega, -- let Lean solve this by itself (using linear integer and natural number arithmetic)
  }
end

/--the nth element of the first m elements is the nth element if n < m-/
lemma nth_le_take {α : Type*} (l : list α) (n m : ℕ) (h1) (h2) :
nth_le (take m l) n h1 = nth_le l n h2 :=
begin
  rw length_take at h1, /- length (take m l) = min m length l 
                           creates duplicate of h1, as h1 in its exact old form
                           is needed as an argument for nth_le-/
  rename h1 h3, -- this line renames the new version of h1
  rw lt_min_iff at h3, -- n < min m (length l) ↔ n < m ∧ n < length l
  cases h3 with H1 H2, -- now H1 : n < m , and H2 : n < length l

  revert m n, -- so the inductive hypothesis holds for any choices of m and n
  induction l with k Lk IH,

    -- base case : l = nil
    { intros m n h1 h2 H1 H2, -- now l = nil contradicts H2, saying n < length l
      exfalso, 
      rw length at H2, -- length nil = 0 by def of length
      cases H2}, -- both cases killed immediately

    -- inductive step : l = (k :: kL) 
    intros m n h1 h2 H1 H2,
    cases m with m',

      -- m = 0
      { simp only [take_zero], -- take 0 (k :: Lk) = nil    (simp only because of nth_le)
          cases H1}, -- both cases killed immediately

      -- m = nat.succ m'  for some natural number m'    
      { simp only [take], /- take (nat.succ m') (k :: Lk) = (k :: take m' Lk)
                             (simp only because of nth_le) -/                    
        cases n with n',

          -- n = 0 
          {refl}, -- by def of nth_le

          -- n = nat.succ n'  for some natural number n'
          {rw nth_le, /- nth_le (k :: take m' Lk) (nat.succ n') _ = nth_le (take m' Lk) n' _
                         by def of nth_le-/
          rw nth_le,  /- nth_le (k :: Lk) (nat.succ n') h2 = nth_le Lk n' _
                         by def of nth_le-/
          apply IH, -- apply inductive hypothesis

          /- IH was ∀ (m n : ℕ) (h1 : n < length (take m Lk)) (h2 : n < length Lk),
             n < m → n < length Lk → nth_le (take m Lk) n h1 = nth_le Lk n h2,
             
             we used it for m' and n'
             h1 and h2 Lean can infer itself, so only need to prove n' < m' and n' < length Lk-/
            {apply nat.lt_of_succ_lt_succ, 
            assumption}, -- true by some assumption (here h1)

            apply nat.lt_of_succ_lt_succ, 
            assumption}, -- true by h2
      }
end



/--the ith element of of_fn f (if it is in the list) is f(i)-/
@[simp] theorem nth_le_of_fn' {α : Type*} {n : ℕ} (f : fin n → α)
  (i : ℕ) (hi : i < n) :
  nth_le (of_fn f) i ((length_of_fn f).symm ▸ hi) = f ⟨i, hi⟩ :=
  -- the following proof is in term mode
option.some.inj $ by rw [← nth_le_nth];
  simp only [list.nth_of_fn, of_fn_nth_val, fin.eta, dif_pos hi]



/- head -/

/--if two lists are equal, their heads are equal-/
lemma head_eq_of_list_eq {α : Type*} [inhabited α] {L1 L2 : list α}:
L1 = L2 → list.head L1 = list.head L2:= 
begin
intro h, -- h is L1 = L2
rw h,
end


/--The head of a list with its first m element dropped is
   its (m+1)th element-/
lemma head_drop (α : Type*) [inhabited α] (L : list α) (m : ℕ) (hm : m < L.length):
  head (drop m L) = nth_le L m hm :=
begin
  revert L, -- so the inductive hyothesis holds for any list of lenght greater m
  induction m with d hd,
    -- base case :  m = 0
    { intros L hL,
      rw drop_zero, -- drop 0 L = L
      rw nth_le_zero,
    },
    -- inductive step : n = nat.succ d
    intros L hm,
    cases L with a M,
        -- L = nil
        {cases hm}, -- does it as hm is equivalent to nat.succ d < 0
      --  L = (a :: M)
      exact hd M _, /- true by inductive hypothesis
                       that d < length M can be inferred from hm -/
  end


/- sum -/

/--the sum of a two-element list is the sum of its two elements-/
theorem sum_list2 (α : Type*) [add_monoid α] (x y : α) : list.sum [x, y] = x + y :=
begin
  -- [x,y] is interpreted as (x :: (y :: nil))
  rw list.sum_cons, -- sum (x :: [y]) = x + sum [y] 
  rw list.sum_cons, -- sum (y :: nil) = y + sum nil 
  rw list.sum_nil, -- sum nil = 0
  rw add_zero, -- y + 0 = 0
end


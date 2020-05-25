import list.simple_value 
       list.modify.basic



open list

/-- Man in the middle for all-chain or all-loop situations -/
theorem MITM_baby (tf : ℤ) (L1 L2 : list ℤ) (d : ℤ) (h : list.modify L1 L2 d)
  (n : ℕ) (hL1 : L1.length = n) (hL2 : L2.length = n) (i : fin n) :
  abs (list.value_i tf n L1 i hL1 - list.value_i tf n L2 i hL2) ≤ d :=
begin
  revert L1 L2,
  induction n with e he,
  cases i.is_lt,
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
    -- now deduce from he somehow!
    --prove 0 <= d from h using that the asolute value is non-negative 
    apply le_trans _ h.bound, 
    show abs (nth_le L1 h.n h.ha - nth_le L2 h.n h.hb) ≥ 0,
    exact abs_nonneg _,

    intros n HnL HnM,
    
    --need this as argument for he (in he L1 = (remove_nth L1 (i.val))
    --and L2 = (remove_nth L2 (i.val)))
    rw eq_comm at hin,
    have P : list.modify (remove_nth L1 (i.val)) (remove_nth L2 (i.val)) d, 
    exact list.modify_remove_nth h i.val hin,
    --the point at which both lists will differ is h_n-1 if h_n > i.val
    --and h_n if h_n < i.val

    rw length_of_fn at HnL,
    rw nth_le_of_fn _ ⟨n, HnL⟩,
    rw nth_le_of_fn _ ⟨n, HnL⟩,

    exact he _ _ _ P _ _,
    }
end

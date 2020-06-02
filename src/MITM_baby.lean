import list.simple_value 
       list.modify.basic



open list

/-- Man in the middle for all-chain or all-loop situations -/
theorem MITM_baby (tf : ℤ) (L1 L2 : list ℤ) (d : ℤ) (h : list.modify L1 L2 d)
  (n : ℕ) (hL1 : L1.length = n) (hL2 : L2.length = n) (i : fin n) :
  abs (list.value_i tf n L1 i hL1 - list.value_i tf n L2 i hL2) ≤ d :=
begin
  revert L1 L2, -- so the inductive hypothesis does not depend on the exact choice of L1 and L2
  induction n with e he, -- by induction on the number of components

    -- base case : n = 0
    {cases i.is_lt},

    -- inductive step : n = nat.succ e
    {intros L1 L2 h hL1 hL2,
    unfold list.value_i,

    /- after unfolding, the goal is :
       abs
       (aux_fun (nth_le L1 (i.val) _) tf (min' (of_fn (λ (j : fin e), value_i tf e (remove_nth L1 (i.val)) j _))) -
        aux_fun (nth_le L2 (i.val) _) tf (min' (of_fn (λ (j : fin e), value_i tf e (remove_nth L2 (i.val)) j _)))) 
        ≤ d
    -/

    /- now either we opened the component in which the games differ or not-/
    by_cases hin : h.n = i.val,
    
      { -- i = place where lists differ
        have heq := h.heq,
        rw hin at heq, -- after substitution, heq is remove_nth L1 (i.val) = remove_nth L2 (i.val)
        simp only [heq], -- simp only rewrites in the arguments of nth_le as well 
        apply list.aux_fun_L1, -- see list.simple_value
        convert h.bound, -- goal is basically just h.bound
          exact hin.symm, /- need to prove i.val = h.n, as the goal described the indices
                             using i.val, and h.bound used h.n-/
          exact hin.symm, -- because i.val/h.n comes up twice
      },

      { -- i ≠ place where lists differ
           /- so this time by another lemma nth_le L1 (i.val) _ = nth_le L2 (i.val) _ -/
        rw list.modify_same h i.val _ (begin rw hL2, exact i.is_lt end) hin, -- see list.modify.basic
        apply list.aux_fun_L2, -- see list.simple_value
        -- apply "lists differ by at most d -> min differs by at most d"
        apply list.min'_change, -- see list.min.basic

          {simp only [list.length_of_fn]}, -- use that length (of_fn (λ (j : fin e), ...))) = e
          
          --prove 0 <= d from h using that the absolute value is non-negative 
          {apply le_trans _ h.bound, -- transitivity of ≤ 
          show abs (nth_le L1 h.n h.ha - nth_le L2 h.n h.hb) ≥ 0, 
          exact abs_nonneg _,}, -- absolute values are non-negative

          {intros n HnL HnM,        
          rw eq_comm at hin, -- commutativity of =

          --need the following as argument for he (in he L1 = (remove_nth L1 (i.val))
          --and L2 = (remove_nth L2 (i.val)))
          have P : list.modify (remove_nth L1 (i.val)) (remove_nth L2 (i.val)) d, 
            {exact list.modify_remove_nth h i.val hin}, -- see list.modify.basic
 
          -- put the goal into the correct form for the inductive hypothis he
          rw length_of_fn at HnL,
          rw nth_le_of_fn _ ⟨n, HnL⟩, /- nth_le (of_fn f) ⟨n, HnL⟩ = f (⟨n, HnL⟩)
                                        (where f is : λ (j : fin e), value_i tf e (remove_nth L1 (i.val)) j _)) -/
          rw nth_le_of_fn _ ⟨n, HnL⟩,

          exact he _ _ _ P _ _, /- use inductive hypothesis 
                                   (every argument other than P can be inferred)-/
          },
      },
   }
end

import data.list.basic tactic.linarith
import tactic.omega tactic.apply
import list.lemmas.simple

open list


/- head -/


/--If you take the head of the first n+1 elements in reverse order you get the nth element-/
lemma head_reverse_take {A : list ℤ} {n : ℕ } (h : n < length A):
  head (reverse (take (n + 1) A)) = nth_le A n h :=
begin
  /- we want to change the LHS to something involving nth_le (to 
     nth_le (reverse (take (n + 1) A)) 0 (H1 : 0 < length (reverse (take (n + 1) A))
     using nth_le_zero)
     For that we need the corresponding argument H1 for nth_le-/
  have H1 : 0 < length (reverse (take (n + 1) A)),
   { rw length_reverse, -- length (reverse (take (n + 1) A)) = length (take (n + 1) A)
     rw length_take, -- length (take (n + 1) A) = min (n + 1) (length A)
     apply lt_min, -- lemma says, for all a,b,c, a < b → a < c → a < min b c
       -- focused goal: 0 < n + 1
       exact nat.succ_pos n, -- lemma says any successor of a natural number is positive
     -- focused goal: 0 < length A
     refine lt_of_le_of_lt _ h, -- using that 0 ≤ n and n < length A imply 0 < length A
     exact zero_le n, --  0 ≤ n 
},
  -- now we have H1 and nth_le_zero gives the following
  have H : head (reverse (take (n + 1) A)) = nth_le (reverse (take (n + 1) A)) 0 H1,
    rw nth_le_zero,
  rw H, 


rw nth_le_reverse' _ _ _ _, -- see list.lemmas.simple
  swap, /- first prove necessary hypothesis for nth_le_reverse' that
          length (take (n + 1) A) - 1 - 0 < length (take (n + 1) A)-/
  { rw length_take, -- length (take (n + 1) A) = min (n + 1) (length A)
    rw nat.sub_zero,
    apply buffer.lt_aux_2, --min (n + 1) (length A) > 0 → min (n + 1) (length A) - 1 < min (n + 1) (length A)
    /- to show min (n + 1) (length A) > 0, we can show that 0 < (n + 1) and n + 1 ≤ length A 
        the second one is h-/
    have H : 0 < (n + 1) := by norm_num, -- the first one is true for any n in ℕ 
    apply lt_of_lt_of_le H, -- n + 1 ≤ min (n + 1) (length A) → min (n + 1) (length A) > 0
    apply le_min (le_refl _), -- n + 1 ≤ length A  → n + 1 ≤ min (n + 1) (length A)
    exact h },
  -- other goal :  nth_le (take (n + 1) A) (min (n + 1) (length A) - 1 - 0) _ = nth_le A n h 
  simp only [length_take], -- simp only because of nth_le
  rw nth_le_take, -- see list.lemmas.simple
    swap, /- solve necessary hypothesis for nth_le_take first, which is
             min (n + 1) (length A) - 1 - 0 < length A-/
  { rw nat.sub_zero, -- get rid of (- 0)
    rw nat.sub_lt_right_iff_lt_add, /- if 1 ≤ min (n + 1) (length A), then min (n + 1) (length A) - 1 < length A ↔ min (n + 1) (length A) < length A + 1
                                       (hyothesis 1 ≤ min (n + 1) (length A) necessary beause 0 - 1 = 0) -/
    { apply lt_of_le_of_lt _ (nat.lt_succ_self _), -- min (n + 1) (length A) ≤ length A → min (n + 1) (length A) < length A + 1
      apply min_le_right}, -- lemma says : min a b ≤ b for all a,b of the same type

    -- now need to prove 1 ≤ min (n + 1) (length A) because of nat.sub_lt_right_iff_lt_add
    apply le_min, -- 1 ≤ n + 1 → 1 ≤ length A → 1 ≤ min (n + 1) (length A)
    -- prove 1 ≤ n + 1
    {exact nat.le_add_left 1 n},
    -- prove 1 ≤ length A
    {show 0 < length A,
     refine lt_of_le_of_lt _ h, -- just like line 26
     exact nat.zero_le n,}
  },

  -- back to main goal : nth_le A (min (n + 1) (length A) - 1 - 0) ?m_1 = nth_le A n h
  congr', -- suffices to show : min (n + 1) (length A) - 1 - 0 = n
  rw nat.sub_zero, -- get rid of (- 0)
  have H3 : n + 1 ≤ length A,
    {exact h},
  rw min_eq_left H3, -- by H3 min (n + 1) (length A) = n + 1
  exact nat.add_sub_cancel n 1,

end






/- remove_nth -/


/--The list with element n removed is the same as the list ccreated by
   appending the list containing all its elements after element n to the 
   list containing its elements up to and excluding element n-/
lemma remove_nth_eq_take_append_drop (n : ℕ) (L : list ℤ) :
  remove_nth L n = take n L ++ drop (n + 1) L :=
begin
  rw remove_nth_eq_nth_tail, -- remove_nth L n = modify_nth_tail tail n L
  rw modify_nth_tail_eq_take_drop, -- modify_nth_tail tail n = take n L ++ tail (drop n L)
  rw tail_drop, /- tail (drop n L) = drop (nat.succ n) L,
                   which is definitionally equal to drop (n + 1) L 
                   by def of nat.succ-/

  -- other goal : tail nil = nil (hypothesis necessary for modify_nth_tail_eq_take_drop)
  refl, -- true by definition of tail
end


/--changing the order of element removal of a list of integers-/
lemma remove_nth_remove_nth {a b : ℕ } (L : list ℤ)(Ha : a ≤ length L)(Hb : b + 1 ≤ length L):
remove_nth (remove_nth L a) b = if a < (b + 1) then remove_nth (remove_nth L (b+1)) a 
else remove_nth (remove_nth L b) (a-1):=
begin
  /- my proof will at some point require a to be psitive, so we prove the case where
     a is 0 separately-/
  cases a,
    -- a = 0 
    { rw if_pos (nat.zero_lt_succ _), -- 0 < (b + 1),  because any successor in ℕ is greater than 0
      -- so we need to prove remove_nth (remove_nth L a) b = remove_nth (remove_nth L (b+1)) 0
      rw remove_nth_zero, -- lemma says : for any list A, remove_nth A 0 = tail A
      rw remove_nth_zero,
      cases L with c Lc,
        -- L = nil
        {intros, 
        refl}, -- both sides are nil by def of remove_nth and tail
        -- L = (c :: Lc)
        {intros,
        refl}, /- both sides are remove_nth (tail (c :: Lc)) b 
                  by def of remove_nth and tail-/
    },
  
  -- nat.succ a
  split_ifs with ite1, -- now we have to prove each case of the if-then-else-condition
    -- if-case (named ite1) :  nat.succ a < b + 1
    { repeat {rw remove_nth_eq_take_append_drop}, -- see lemma above
      /- get goal : take b (take (nat.succ a) L ++ drop (nat.succ a + 1) L) ++
      drop (b + 1) (take (nat.succ a) L ++ drop (nat.succ a + 1) L) =
      take (nat.succ a) (take (b + 1) L ++ drop (b + 1 + 1) L) ++
      drop (nat.succ a + 1) (take (b + 1) L ++ drop (b + 1 + 1) L)
      
      we need to simplify this
      We will start by getting rid of appends within drop or take-/

      rw drop_append, /- drop (b + 1) (take (nat.succ a) L ++ drop (nat.succ a + 1) L) =
                        ite (b + 1 ≤ length (take (nat.succ a) L)) (drop (b + 1) (take (nat.succ a) L) ++ drop (nat.succ a + 1) L)
                        (drop (b + 1 - length (take (nat.succ a) L)) (drop (nat.succ a + 1) L))-/
      split_ifs with ite2,
        -- if-case (named ite2) : b < length (take (nat.succ a) L)
          {rw [length_take, lt_min_iff] at ite2, --b < length (take (nat.succ a) L) ↔ b < nat.succ a ∧ b < length L
          cases ite2, 
          linarith}, -- gives contradiction between ite1 and b < nat.succ a which Lean can find itself with linarith
        
        -- else-case (named ite2) : ¬ (b < length (take (nat.succ a) L))
        clear ite2,-- will not need negation of ite2 for this 
        rw @take_append _ _ _ (a + 1), /- take (nat.succ a) (take (b + 1) L ++ drop (b + 1 + 1) L) 
                                          = ite (a + 1 ≤ length (take (b + 1) L)) (take (a + 1) (take (b + 1) L))
                                            (take (b + 1) L ++ take (a + 1 - length (take (b + 1) L)) 
                                            (drop (b + 1 + 1) L))-/                                    
        split_ifs with ite3,
          swap,

          -- else-case (named ite3) : ¬ (a < length (take (b + 1) L))
          { push_neg at ite3, -- ite3 is length (take (b + 1) L) ≤ a
            rw [length_take] at ite3, -- ite3 ↔ min (b + 1) (length L) ≤ a
            exfalso, -- gives contradiction between ite3 and ite1
            rw min_eq_left Hb at ite3, -- know (by Hb) that the minimum is b+1
              change a + 1 < _ at ite1,
              linarith, -- after simplifying ite1 Lean can find the contradiction
          },

          -- if-case (named ite3) :  a < length (take (b + 1) L)
          rw take_append,-- get rid of the other append within take
          rw drop_append,-- get rid of the other append within drop

          /- simplifying the if-conditions that came up in the last two lines :
          b ≤ length (take (nat.succ a) L)  and  nat.succ a + 1 ≤ length (take (b + 1) L)-/
          rw length_take,
          rw length_take,
          rw min_eq_left Hb,
          rw min_eq_left Ha,
          rw nat.succ_eq_add_one at *, -- nat.succ a = a + 1 (rewritten in all hypotheses as well)
          -- now they are b ≤ a + 1 and a + 1 + 1 ≤ b + 1 (the second one is true by ite1 : a + 1 < b + 1)
          clear ite3,
          rw if_pos (show a+1+1≤b+1, from ite1), -- second if-condition is true by ite1
          split_ifs with ite4, -- the other we solve by cases 

          --if-case (named ite4) : b ≤ a + 1
          { rw le_iff_eq_or_lt at ite4, -- ite4 is b = a + 1 ∨ b < a + 1
            cases ite4,
              swap, 

              -- b < a + 1
              {exfalso, -- contradicts ite1
              linarith},

              -- b = a + 1
              {rw ←ite4, -- express everything in terms of b and L
              /- goal is :
                take b (take b L) ++ drop (b + 1 - b) (drop (b + 1) L) =
                take b (take (b + 1) L) ++ (drop (b + 1) (take (b + 1) L) ++ drop (b + 1 + 1) L)-/
              rw take_take, -- take b (take b L) = take (min b b) L
              rw min_self, -- min b b = b
              rw take_take, -- take b (take (b + 1) L) = take (min b (b + 1)) L
              rw min_eq_left, -- min b (b + 1) = b, need to prove b ≤ b + 1 for that
                swap, 
                {simp only [zero_le, le_add_iff_nonneg_right]}, -- proves b ≤ b + 1
              congr', /- changes goal to drop (b + 1 - b) (drop (b + 1) L) = 
                        drop (b + 1) (take (b + 1) L) ++ drop (b + 1 + 1) L -/
              rw drop_drop, -- drop (b + 1 - b) (drop (b + 1) L) = drop (b + 1 - b + (b + 1)) L
              rw drop_take (b+1) 0 L, -- drop (b + 1) (take (b + 1) L) = take 0 (drop (b + 1) L)
              rw take_zero, -- take 0 (drop (b + 1) L) = nil
              rw nil_append, 
              -- goal is now drop (b + 1 - b + (b + 1)) L = drop (b + 1 + 1) L
              simp,}, -- Lean can do this by itself with simp
          },

            --else-case (named ite4) : ¬ (b ≤ a + 1)
            { /- goal is again :
                take (a + 1) L ++ take (b - (a + 1)) (drop (a + 1 + 1) L) 
                ++ drop (b + 1 - (a + 1)) (drop (a + 1 + 1) L) =
                take (a + 1) (take (b + 1) L) ++ (drop (a + 1 + 1) (take (b + 1) L) 
                ++ drop (b + 1 + 1) L)-/
              rw drop_drop, /- drop (b + 1 - (a + 1)) (drop (a + 1 + 1) L) =  
                              drop (b + 1 - (a + 1) + (a + 1 + 1)) L -/
              rw take_take, /- take (a + 1) (take (b + 1) L) =
                                take (min (a + 1) (b + 1)) L-/
              rw min_eq_left (le_of_lt ite1), -- min (a + 1) (b + 1) = a + 1 , because of ite1
              rw ←drop_take, /- take (b - (a + 1)) (drop (a + 1 + 1) L) = 
                                drop (a + 1 + 1) (take (a + 1 + 1 + (b - (a + 1))) L) -/

              /- hence have goal : 
                take (a + 1) L ++ drop (a + 1 + 1) (take (a + 1 + 1 + (b - (a + 1))) L) 
                ++ drop (b + 1 - (a + 1) + (a + 1 + 1)) L =
                take (a + 1) L ++ (drop (a + 1 + 1) (take (b + 1) L) ++ drop (b + 1 + 1) L)
              
              
                Just need to show the terms in brackets are the same on both sides-/
              have p1 : b + 1 - (a + 1) + (a + 1 + 1) = b + 1 + 1,
                  {clear Hb Ha, -- because omega peculiarly does not work otherwise
                  omega}, -- Lean can solve this by itself
              rw p1,
              clear p1,
              have p2 : a + 1 + 1 + (b - (a + 1)) = b + 1,
                  {clear Hb Ha, -- because omega peculiarly does not work otherwise
                  omega}, -- Lean can solve this by itself
              rw p2,
              clear p2,
              simp,
              },

    },

    -- else-case (named ite1) : ¬ (nat.succ a < b + 1)
    { rw nat.succ_eq_add_one at *,
      repeat {rw remove_nth_eq_take_append_drop},
      /- goal is now in form :
         take b (take (a + 1) L ++ drop (a + 1 + 1) L) 
         ++ drop (b + 1) (take (a + 1) L ++ drop (a + 1 + 1) L) =
         take (a + 1 - 1) (take b L ++ drop (b + 1) L) 
         ++ drop (a + 1 - 1 + 1) (take b L ++ drop (b + 1) L)
         
         Again, we need to simplify this-/
      rw take_append, /- take b (take (a + 1) L ++ drop (a + 1 + 1) L) =
                         if (b ≤ length (take (a + 1) L)) then (take b (take (a + 1) L))
                         else (take (a + 1) L ++ take (b - length (take (a + 1) L)) (drop (a + 1 + 1) L))-/
      split_ifs with ite5,
        swap,
        -- else-case (named ite5) : ¬ (b ≤ length (take (a + 1) L))
        {exfalso, -- contradicts ite1 (rewrite ite5 until Lean finds the contradiction with linarith)
        push_neg at ite5,
        rw length_take at ite5,
        rw min_eq_left Ha at ite5,
        linarith},

        -- if-case (named ite5) : b ≤ length (take (a + 1) L)
        {rw drop_append, /- drop (b + 1) (take (a + 1) L ++ drop (a + 1 + 1) L) =
                            if (b + 1 ≤ length (take (a + 1) L)) then (drop (b + 1) (take (a + 1) L) ++ drop (a + 1 + 1) L)
                            else (drop (b + 1 - length (take (a + 1) L)) (drop (a + 1 + 1) L)-/
        push_neg at ite1, -- put ite5 in form b + 1 ≤ a + 1
        -- simplify if-condition
        rw length_take, -- length (take (a + 1) L) = min (a + 1) (length L)
        rw min_eq_left Ha, -- min (a + 1) (length L) = a + 1 because of Ha
        rw if_pos ite1, -- if-condition is exactly ite1, so is true
        rw drop_append, /- drop (a + 1 - 1 + 1) (take b L ++ drop (b + 1) L) =
                           if (a + 1 - 1 + 1 ≤ length (take b L)) 
                           then (drop (a + 1 - 1 + 1) (take b L) ++ drop (b + 1) L)
                           else (drop (a + 1 - 1 + 1 - length (take b L)) (drop (b + 1) L))-/
        split_ifs with ite6,
          
          -- if-case (named ite6) : a + 1 - 1 + 1 ≤ length (take b L)
          rw length_take at ite6, -- length (take b L) = min b (length L)
          rw min_eq_left (le_trans (nat.le_succ b) Hb) at ite6, -- min b (length L) = b (because of Hb and transitivity of ≤)
            {exfalso, -- ite6 contradicts ite1
            clear Ha Hb ite5,
            omega}, 
          
          -- else-case (named ite6) : ¬ (a + 1 - 1 + 1 ≤ length (take b L))
          rw take_append, /- take (a + 1 - 1) (take b L ++ drop (b + 1) L) =
                             if (a + 1 - 1 ≤ length (take b L)) 
                             then (take (a + 1 - 1) (take b L))
                             else (take b L ++ take (a + 1 - 1 - length (take b L)) 
                             (drop (b + 1) L))-/
              -- simplify if-condition to a + 1 - 1 ≤ b
          rw length_take,
          rw min_eq_left (le_trans (nat.le_succ b) Hb),

          split_ifs with ite7,

            -- if-case (named ite7) : a + 1 - 1 ≤ b
            {push_neg at ite6, -- put ite6 in form length (take b L) ≤ a + 1 - 1
            have eq: a + 1 - 1 = b,
              {rw length_take at ite6, 
              rw min_eq_left (le_trans (nat.le_succ b) Hb) at ite6,
              exact le_antisymm ite7 ite6}, -- ite6 is now b ≤ a + 1 - 1, so with ite7 we have equality
            rw nat.add_sub_cancel at eq, -- get rid of 1 - 1 in eq
            rw eq, -- express everything in terms of b and L
            rw nat.add_sub_cancel, -- get rid of 1 - 1

            /- goal is now :
               take b (take (b + 1) L) ++ (drop (b + 1) (take (b + 1) L) 
               ++ drop (b + 1 + 1) L) =
               take b (take b L) ++ drop (b + 1 - b) (drop (b + 1) L)-/

            rw take_take, --take b (take (b + 1) L) = take (min b (b + 1) L)
            rw min_eq_left (nat.le_succ b), -- min b (b + 1) = b (as b ≤ b + 1)
            rw drop_drop, -- drop (b + 1 - b) (drop (b + 1) L) = drop (b + 1 - b + (b + 1)) L
            rw take_take, -- take b (take b L) = take (min b b) L
            clear eq,
            rw min_eq_left (nat.le_refl b), -- min b b, because of reflexivity of ≤ 
            simp only [add_zero, nat.add_sub_cancel_left, add_comm, le_add_iff_nonneg_right],
            rw append_left_inj (take b L), /- take b L ++ (drop (b + 1) (take (b + 1) L) ++ drop (1 + (b + 1)) L) = 
                                              take b L ++ drop (1 + (b + 1)) L
                                              ↔
                                              (drop (b + 1) (take (b + 1) L) ++ drop (1 + (b + 1)) L) = 
                                              drop (1 + (b + 1)) L-/
            rw drop_take (b + 1) 0 L, -- drop (b + 1) (take (b + 1) L) = take 0 (drop (b + 1) L)
            rw take_zero, --take 0 (drop (b + 1) L) = nil
            rw nil_append,},

            -- else-case (named ite7) : ¬ (a + 1 - 1 ≤ b)
            /- goal is :
               take b (take (a + 1) L) ++ (drop (b + 1) (take (a + 1) L) 
               ++ drop (a + 1 + 1) L) =
               take b L ++ take (a + 1 - 1 - b) (drop (b + 1) L) 
               ++ drop (a + 1 - 1 + 1 - b) (drop (b + 1) L)-/

            {clear ite6,
            rw take_take, -- take b (take (a + 1) L) = take (min b (a + 1)) L
            rw drop_drop, -- drop (a + 1 - 1 + 1 - b) (drop (b + 1) L) = drop (a + 1 - 1 + 1 - b + (b + 1)) L
            rw length_take at ite5, -- so ite 5 is :  b ≤ min (a + 1) (length L)
            rw min_eq_left Ha at *, -- min (a + 1) (length L) = a + 1 , because of Ha  (everywhere)
            rw min_eq_left ite5 at *, -- min b (a + 1) = b , because of ite5  (everywhere)
            rw ← drop_take, -- take (a + 1 - 1 - b) (drop (b + 1) L) = drop (b + 1) (take (b + 1 + (a + 1 - 1 - b)) L)

            /- so goal is :
                take b L ++ (drop (b + 1) (take (a + 1) L) ++ drop (a + 1 + 1) L) =
                take b L ++ drop (b + 1) (take (b + 1 + (a + 1 - 1 - b)) L) 
                ++ drop (a + 1 - 1 + 1 - b + (b + 1)) L
            
            and both sides are the same after simpifying the arithmetic-/
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
            simp}, -- basically would just need associativity of append
    },
  },
end

/-- If two lists each with their nth element removed are the same,
    then their lengths are the same-/
lemma remove_nth_eq_remove_nth_to_length_eq {α : Type*} {A B : list α}:
∀ (n : ℕ) (hA : n < length A)(hB : n < length B), remove_nth A n = remove_nth B n 
→ length A = length B:=
begin
intros n hA hB h,
-- show the length of the shortened lists are the same
have p : length (remove_nth A n) = length (remove_nth B n), 
  {rw h},
-- show from that length A - 1 = length B - 1
rw length_remove_nth A n hA at p,
rw length_remove_nth B n hB at p,
/- as length A is a natural number, length A - 1 = 0 if length A = 0 in Lean,
   so we need the following, which follow from hA and hB 
   (the leangths are strictly greater than some natural number, so at least 1)-/
have pa : 1 ≤ length A := by exact nat.one_le_of_lt hA, 
have pb : 1 ≤ length B := by exact nat.one_le_of_lt hB, 
exact nat.pred_inj pa pb p, -- now through pa and pb and p the result follows 
end


/- drop -/

/-- If the index of the removed element is less than the amount b one wants to drop from the start,
    it is the same as dropping b + 1-/
lemma drop_remove_nth_le {a b : ℕ } {L : list ℤ} (h1 : a ≤ b) (h2 : b ≤ length L):
drop b (remove_nth L a) = drop (b + 1) L :=
begin
rw remove_nth_eq_take_append_drop,-- remove_nth L a = take a L ++ drop (a + 1) L
  rw drop_append, /- drop b (take a L ++ drop (a + 1) L) =
                     if (b ≤ length (take a L)), 
                     then (drop b (take a L) ++ drop (a + 1) L),
                     else (drop (b - length (take a L)) (drop (a + 1) L))-/
  rw length_take, -- length (take a L) = min a (length L)
  rw min_eq_left (le_trans h1 h2), -- min a (length L) = a, because of h1 and h2
  split_ifs with ite,
    -- if-case (named ite) :  b ≤ a (in this case because of h1, a = b)
    {
    {have p1: a=b:= by exact le_antisymm h1 ite,
    rw p1,
    -- the statement then holds because drop b (take b L) = nil (we drop all we take)
    have p2 : drop b (take b L) = nil,
      {convert drop_all _,
      rw length_take,
      rw min_eq_left h2,},
    rw p2,
    rw nil_append}, -- nil ++ drop (b + 1) L = drop (b + 1) L
    },
    
    -- else-case (named ite) :  ¬ (b ≤ a)
    {rw drop_drop, -- drop (b - a) (drop (a + 1) L) = drop (b - a + (a + 1)) L
     congr' 1, /- instead of drop (b - a + (a + 1)) L = drop (b + 1) L
                  we can prove b - a + (a + 1) = b + 1 -/
     show b - a + a + 1 = b + 1,
     rw nat.sub_add_cancel h1,
    },
end


/--If dropping the first x elements of two lists gives the same list, 
   so does dropping the first x + 1-/
lemma drop_aux_1 {A B : list ℤ} {x: ℕ } :
drop x A = drop x B → drop (nat.succ x) A = drop (nat.succ x) B :=
begin 
intro H,
rw nat.succ_eq_add_one, 
rw add_comm,
rw drop_add, -- lemma says : for all a, b in ℕ, lists L, drop (a + b) L = drop a (drop b L)
rw H,
rw drop_drop, -- drop_add backwards
end

/--If dropping the first x elements of two lists gives the same list, 
so does dropping the first y if y ≥ x-/
lemma drop_aux_2 {A B : list ℤ} {x y : ℕ } (h : x ≤ y):
drop x A = drop x B → drop y A = drop y B :=
begin
/- The plan is to use induction on the difference n between x and y,
   then if n = 0 this is trivial and the inductive step is done using drop_aux_1-/
have P : ∃ (n:ℕ), y = x + n, 
  {exact le_iff_exists_add.mp h},
cases P with n Pn, -- let n be s.t. (Pn : y = x + n)  holds
have Py : x = y - n,
  {rw Pn, 
   rw nat.add_sub_cancel}, -- n and -n cancel
rw Py,
revert A B x y, -- do not want inductive hypothesis to depend on A,B,x,y
induction n with d hd,
    -- base case : n = 0
    {repeat {rw nat.add_zero}, -- x + 0 = x
    simp}, -- Lean can do this much by itself

    -- inductive step : n = nat.succ d
    {intros A B x y P Py Px H, -- A B x y P Py Px as before
    rw nat.succ_eq_add_one at Py, 
    rw Py,
    rw ← add_assoc, -- associativity of +
    -- goal is now : drop (x + d + 1) A = drop (x + d + 1) B
    rw drop_add,  -- lemma says : for all a, b in ℕ, lists L, drop (a + b) L = drop a (drop b L)
    rw drop_add (x+d) 1 B,
    /- now the goal is drop (x + d) (drop 1 A) = drop (x + d) (drop 1 B)
       that is why we had to revert A and B
       this is the correct form for the inductive hypothesis
       with x = x , y = x + d, A = drop 1 A, B = drop 1 B
       but before we can use it we need a few trivial necessary hypotheses for 
       hd-/
    rw ← Px at H,
    have triv1 : x ≤ x + d, simp,
    have triv2 : x + d = x + d, refl,
    have triv3 : x = x + d - d, simp,
    have H_new : drop (nat.succ x) A = drop (nat.succ x) B,
       {exact drop_aux_1 H},
    -- need H_new in the form : drop (x + d - d) (drop 1 A) = drop (x + d - d) (drop 1 B)
    rw nat.succ_eq_add_one at H_new,
    rw drop_add at H_new, 
    rw drop_add x 1 B at H_new,
    rw triv3 at H_new,

    exact hd triv1 triv2 triv3 H_new}, -- use inductive hypothesis

end



/- take -/

/--If the first x+1 elements of two lists are the same, so are the first x-/
lemma take_aux_1 {A B : list ℤ} {x: ℕ } :
take (nat.succ x) A = take (nat.succ x) B → take x A = take x B :=
begin 
revert B x, -- so inductive hypothesis does not depend on x or B
induction A with a An IH,

  -- base case : A =  nil
  {intros B x,
  cases B with b Bn, -- because we get a contradiction when B is non-empty

    -- B = nil
    { intro H,
      refl}, -- clearly take x nil = take x nil

    -- B = (b :: Bn)
    {intro H,
    exfalso, /- contradicts H : take (nat.succ x) nil = take (nat.succ x) (b :: Bn)
                as RHS is not nil -/
    rw take_nil at H, -- take (nat.succ x) nil
    rw take_cons at H, -- take (nat.succ x) (b :: Bn) = b :: take x Bn
    simp at H, -- Lean sees that H is false by itself
    exact H}},

  -- inductive step : A = (a :: An)
  {intros B x,
  cases B with b Bn, -- because we get a contradiction when B is empty

    -- B = nil  (similar to A = nil and B = (b :: Bn))
    {intro H,
    exfalso,
    rw take_nil at H,
    rw take_cons at H,
    simp at H,
    exact H},
    
    -- B = (b :: Bn)
    /- goal is now : take (nat.succ x) (a :: An) = take (nat.succ x) (b :: Bn) 
                     → take x (a :: An) = take x (b :: Bn)-/
    cases x with y, /- we want to have some successor nat.succ y in place of x
                      because we want to use the inductive hypothesis with Bn and y
                      So we need to do the trivial x=0-case separately-/
      
      -- x = 0
      {intro H,
      rw take_zero, -- lemma says : take 0 L = nil , for any list L
      rw take_zero},
      
      -- x = nat.succ y
      {intro H,
      rw take_cons, /- Lemma says : for any list l, m of the correct type, n in ℕ,  \
                                    take (nat.succ n) (m :: l) = m :: take n l-/
      rw take_cons,
      rw take_cons at H,
      rw take_cons at H,

      /- now from H we need to extract the information that a = b (or 
         equivalently [a] = [b]), and that
         take (nat.succ y) An = take (nat.succ y) Bn. The second one we 
         need for the inductive hypothesis-/

      rw cons_eq_sing_append at H, -- see list.lemmas.simple
      rw cons_eq_sing_append b at H,

      have H_left : [a] = [b] , 
        {rw append_inj_right H _, /- if length [a] = length [b] then [a] = [b]
                                     (because by H, [a] ++ take (nat.succ y) An = [b] ++ take (nat.succ y) Bn-/
        simp},
      have H_right : take (nat.succ y) An = take (nat.succ y) Bn,
        {rw append_inj_left H _,  -- same as above, but equality of the right side of the append
         rw H_left},

      rw cons_eq_sing_append,
      rw cons_eq_sing_append b,
      rw H_left,
      rw append_left_inj [b], -- [b] ++ take y An = [b] ++ take y Bn ↔ take y An = take y Bn
      exact IH H_right},}, -- use inductive hypothesis
end


/--If the first x elements of two lists are the same, so are the first y if y ≤ x-/
lemma take_aux_2 {A B : list ℤ} {x y : ℕ } (h : y ≤  x):
take x A = take x B → take y A = take y B :=
begin
/- The plan is to use induction on the difference n between x and y,
   then if n = 0 this is trivial and the inductive step is done using take_aux_1-/
have P : ∃ (n:ℕ), x = y + n, 
  {exact le_iff_exists_add.mp h},
cases P with n Pn, -- let n be s.t. (Pn : y = x + n)  holds
have Py : y = x - n,
  {rw Pn, 
  rw nat.add_sub_cancel},
rw Py,

revert A B x y, -- so inductive hypothesis does not depend on A B x y
induction n with d hd,

  -- base case : n = 0
  {repeat {rw nat.sub_zero},
  simp}, -- Lean can solve take x A = take x B → take x A = take x B

  -- inductive step : n = nat.succ d
  {intros A B x y P Px Py H,
   rw ← Py,

  /- H is take x A = take x B, so if one of the lists is nil while the 
     other is not, and x is non-zero, we get a contradiction, 
     because only one side will be the empty list -/
  cases A with a An,

    -- A = nil
    {cases B with b Bn,
      
      -- B = nil
      {refl}, -- if both lists are nil, the result follows from def of take

      -- B = (b :: Bn)
      {cases y with y',

        -- y = 0  
        /-(in this case x - nat.succ d = 0, so right side is take 0 (b :: Bn)
           which is also nil)-/
        {rw take_nil, 
        rw take_zero}, 

        -- y = nat.succ y'
        {exfalso, -- y ≤ x, so x is positive
        rw take_nil at H, 
        rw Px at H,
        rw take_cons at H,
        simp at H,
        exact H},},
    },   

    -- A = (a :: An)
    {cases B with b Bn,

      -- B = nil  (similar to case where A = nil and B = (b :: Bn))
      {cases y with y',

        -- y = 0  
        {rw take_nil, 
        rw take_zero},

        -- y = nat.succ y'
        {exfalso,
        rw take_nil at H, 
        rw Px at H,
        rw take_cons at H,
        simp at H,
        exact H},},

      -- B = (b :: Bn)  (main case, where we will need hd)
      /- now the goal is take (x - nat.succ d) (a :: An) = take (x - nat.succ d) (b :: Bn)
       this is the correct form for the inductive hypothesis
       with x = nat.succ y' + d , y = nat.succ y', A = An, B = Bn, for some y'
       so we want y in the form nat.succ y' and hence need to do the (y = 0)-case 
       separately again-/
      {cases y with y', 

        -- y = 0 (here both sides are nil again)
        {rw take_zero,
        rw take_zero},

        -- y = nat.succ y'

        {rw take_cons,
        rw take_cons,
        /- now from H we need to extract the information that a = b (or 
         equivalently [a] = [b]), and that
         take (nat.succ y' + d) An = take (nat.succ y' + d) Bn. The second one we 
         need to get a necessary hypothesis for the inductive hypothesis
         through take_aux_1-/

        rw Px at H,
        rw take_cons at H,
        rw take_cons at H,
        rw cons_eq_sing_append at H,
        rw cons_eq_sing_append b at H,

        have H_left : [a] = [b] , 
          {rw append_inj_right H, 
          simp},
        have H_right : take (nat.succ y' + d) An = take (nat.succ y' + d) Bn,
          {rw append_inj_left H, 
          simp},

        -- similarly to the proof of take_aux_1, we get rid of a and b in the goal
        rw cons_eq_sing_append,
        rw cons_eq_sing_append b,
        rw H_left,
        rw append_left_inj [b],

        -- now we create all the trivial hypotheses needed for the induction
        have triv1 : y' ≤ y' + d, simp,
        have triv2 : y' + d = y' + d, refl,
        have triv3 : y' = y' + d - d, simp,
        have H_new : take (y' + d) An = take (y' + d) Bn, -- H_new can be derived from H
          {rw nat.succ_add at H_right,
          exact take_aux_1  H_right},

        rw triv3, -- put the goal in the exact form of the result of the inductive hypothesis
        exact hd triv1 triv2 triv3 H_new},},}, -- use inductive hypotheses
  }
end


/--If you take the first m+1 elements of a list, revert the order and take the head 
of the resulting list, you get the same element as when you drop the first m-1 elements,
and take the head and then the tail. (You get the m-th element counting from 0)-/
lemma take_drop_head_eq {A:list ℤ} {m : ℕ} (h1: 1 ≤ m) (h2: m + 1 ≤ length A):
head (reverse (take (m+1) A)) = head (tail (drop (m-1) A)):=
-- proof in term mode
by rw [
       tail_drop, head_reverse_take h2, nat.succ_eq_add_one, 
       nat.sub_add_cancel h1, head_drop
       ]
/-
begin
  rw tail_drop,                  
            -- tail (drop (m - 1) A) = drop (nat.succ (m - 1)) A
  rw head_reverse_take h2, 
            -- head (reverse (take (m + 1) A)) = nth_le A m h2
  rw [nat.succ_eq_add_one, nat.sub_add_cancel h1],
            -- nat.succ (m - 1) = m , because 1 ≤ m
  rw head_drop,
            -- head (drop m A) = nth_le A m _
end
-/

/--If you take the first d+2 elements of a list, revert the order and take the head 
of the resulting list, you get the same element as when you drop the first d elements,
and take the head and then the tail. (You get the (d+1)th element element counting from 0)-/
lemma take_drop_head_eq' {A:list ℤ} {d : ℕ} (h2: d + 2 ≤ length A):
head (reverse (take (d+2) A)) = head (tail (drop d A)):=
-- proof in term mode (proof similar to lemma above)
by rw [tail_drop, head_reverse_take h2, head_drop]





/- nth_le -/

/--the nth element of a list with an element removed is the bth or (b+1)th 
element of the full list, depending on which element was removed-/
lemma nth_le_remove_nth {a b : ℕ } (L : list ℤ) (h:b < length (remove_nth L a)) (h1 h2):
nth_le (remove_nth L a) b h = 
if a ≤ b then nth_le L (b+1) h1
else nth_le L b h2:=
begin
split_ifs with ite1,
  -- if-case (named ite1) : a ≤ b
  {rw ← head_drop, -- nth_le (remove_nth L a) b h = head (drop b (remove_nth L a))
  rw ← head_drop,  -- nth_le L (b + 1) h1 = head (drop (b + 1) L)
  apply head_eq_of_list_eq, -- if the lists are equal, their heads are equal
  rw drop_remove_nth_le ite1 (le_of_lt h2), -- now the goal is just the result this lemma (see line 396)
  },

  -- else-case (named ite1) : ¬ (a ≤ b)
  {{repeat {rw ← head_drop},-- goal becomes : head (drop b (remove_nth L a)) = head (drop b L)
  push_neg at ite1, -- puts ite1 in form b < a
  /- this time the lists we are taking the head of are not equal, as drop b (remove_nth L a)
      has one element less than drop b L-/
  rw remove_nth_eq_take_append_drop, -- remove_nth L a = drop b (take a L ++ drop (a + 1) L)
  rw drop_append, /- drop b (take a L ++ drop (a + 1) L) =
                     if (b ≤ length (take a L)), 
                     then (drop b (take a L) ++ drop (a + 1) L),
                     else (drop (b - length (take a L)) (drop (a + 1) L))-/
  rw length_take,
  rw if_pos (le_min (le_of_lt ite1) (le_of_lt h2)), -- we have b ≤ length (take a L), because b < a by ite1 and b < length L by h2
  
  /- we want to use that head (drop b (take a L) ++ drop (a + 1) L) 
     = head (drop b (take a L), because drop b (take a L) is not nil, as b < a and b < length L
     so we need to prove the following as well:-/
  have P : drop b (take a L) ≠ nil,
    {apply ne_nil_of_length_eq_succ , /- we prove this by proving length (drop b (take a L))
    is the successor of some natural number (so greater than 0),
    that natural number is (min a (length L) - b - 1)-/
      swap, 
      {exact min a (length L) - b - 1},  
    rw length_drop, -- length (drop b (take a L)) = length (take a L) - b
    rw length_take, -- length (take a L) = min a (length L)
    rw nat.succ_eq_add_one, --nat.succ (min a (length L) - b - 1) =  min a (length L) - b - 1 + 1
    rw nat.sub_add_cancel, /- min a (length L) - b - 1 + 1 = min a (length L) - b, as reqired,
                              if min a (length L) - b ≥ 1  (because 0 - 1 = 0 in ℕ )-/
    show 1 ≤ (min a (length L)) - b, -- use ≤ , because ≥ is defined via ≤ 
    apply nat.le_sub_right_of_add_le, -- 1 + b ≤ min a (length L) → 1 ≤ min a (length L) - b
    apply le_min, -- suffices to prove 1 + b ≤ a and 1 + b ≤ length L 
    rw add_comm,
    exact ite1, -- first one is true by ite1 (b < a)
    rw add_comm,
    exact (le_of_lt h1),}, -- second one by h1 (b < length L)

  rw head_append _ P, -- now we can use that
  /- The goal is now : head (drop b (take a L)) = head (drop b L)
     
     we will put  head (drop b L) in the form head (drop b (take a L) ++ something)
     and then use head_append again-/
  rw ← take_append_drop a L, -- drop b L = drop b (take a L ++ drop a L) 
  rw drop_append, /- drop b (take a L ++ drop a L) =
                     if (b ≤ length (take a L)),
                     then  (drop b (take a L) ++ drop a L),
                     else (drop (b - length (take a L)) (drop a L)))-/
  rw length_take, 
  rw if_pos (le_min (le_of_lt ite1) (le_of_lt h2)), -- we have b ≤ length (take a L), because b < a by ite1 and b < length L by h2
  rw take_append_drop a L, -- revert the change of the LHS from line 797
  rw head_append _ P, -- head (drop b (take a L) ++ drop a L) = head (drop b (take a L)) by P

},},
end










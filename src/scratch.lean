import data.multiset 

definition multiset.N_min : multiset ℕ → ℕ := sorry 

def value_aux' : multiset ℕ → multiset ℕ → ℕ
| C L := multiset.N_min (multiset.pmap 
      (λ a (h : a ∈ C), 
        have multiset.card (C.erase a) < multiset.card C,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card (C.erase a) + multiset.card L < multiset.card C + multiset.card L, 
--          from add_lt_add_right (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
        a - 2 + int.nat_abs (2 - value_aux' (C.erase a) L))
        C (λ _,id) + multiset.pmap 
      (λ a (h : a ∈ L), 
        have multiset.card (L.erase a) < multiset.card L,
          from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
--        have multiset.card C + multiset.card (multiset.erase L a) < multiset.card C + multiset.card L, 
--          from add_lt_add_left (multiset.card_lt_of_lt (multiset.erase_lt.2 h)) _,
        a - 4 +int.nat_abs (4 - value_aux' C (L.erase a)))
        L (λ _,id))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf 
  (λ CL, multiset.card CL.fst + multiset.card CL.snd)⟩]}


definition x : with_top ℕ := some 6
definition y : with_top ℕ := some 5 
#reduce x + y

definition topadd : with_top ℕ → with_top ℕ → with_top ℕ := has_add.add 
#print topadd 
definition topadd' : has_add (with_top ℕ) := by apply_instance 
#print topadd'
definition topsem : add_semigroup (with_top ℕ) := by apply_instance 
#print topsem 
#print with_top.add_semigroup 
definition topcom : add_comm_semigroup (with_top ℕ) := by apply_instance 
#print topcom

definition F : multiset ℕ → ℕ := begin
intro C,
refine multiset.strong_induction_on C _,
intro D,
intro H,
apply multiset.sum,
apply multiset.pmap (λ a (h : a ∈ D),H (multiset.erase D a) (multiset.erase_lt.2 h)),
exact λ _,id,
end 

def F₂ : multiset ℕ → ℕ
| C := multiset.sum (multiset.pmap (λ a (h : a ∈ C),
  have multiset.card (multiset.erase C a) < multiset.card C, 
    from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
 F₂ (multiset.erase C a)) 
  C (λ _, id))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf multiset.card⟩]}

#print F₂.equations._eqn_1
#print F
#print prefix F
import game.modify.basic  game.value 




open game
open list

/-- the values of two games, that differ in exactly one component by at most d
d, differ by at most d-/
theorem MITM (G1 G2 : game 2) (d : ℤ) (h1 : game.modify G1 G2 d):
 abs(G1.value - G2.value) ≤ d :=
begin
  revert G1,
  revert G2,
  -- induction on size of G2
  apply @game.rec_on_size2 (λ G2, ∀ G1, modify G1 G2 d → 
  abs (game.value G1 - game.value G2) ≤ d),
  -- this might be tricky!
  { -- base case
  intros G h1, have h3 : G.size2 = (zero 2).size2 := eq_size_of_modify h1,
  rw size2_zero at h3, have H := eq_zero_of_size2_zero _ h3, 
  rw H, show  0 ≤ d, exact abs_le_nonneg h1.hl.bound,},
  { -- inductive step
    intros n H G1 p G2 p2,
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
    { 
      have lengthf0 : length (G2.f 0) = length (G1.f 0),
        apply eq_list_lengths_of_modify p2,
      have hi2 : i < length (G1.f 0),
        rw ←lengthf0, exact hi,
      rw nth_le_append _ _,
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
      { 
        /-swap,
        { rw game.size2_remove,
          rw hs,
          exact nat.add_sub_cancel n 1,
        },-/
        set p2l := p2.hl with hp2l,
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

          have nth_le_eq : nth_le (G2.f 0) i hi = nth_le (G1.f 0) i hi2,
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
          rw nth_le_eq,
        /-
          swap,
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },-/
          suffices : abs
            (abs (2 - game.value (game.remove G2 0 ⟨i, hi⟩)) -
             abs (2 - game.value (game.remove G1 0 ⟨i, hi2⟩))) ≤ d,
          { convert this using 2,
            rw [(show ((0 : fin 2).val : ℤ) = 0, by norm_cast), mul_zero, zero_add],
            ring,
          },
          apply le_trans (abs_abs_sub_abs_le _ _),
        have ho : 0 ≠ p2.j ∨ (0 = p2.j ∧ ((⟨i, hi⟩ : fin (length (G2.f 0))).val) ≠ p2.hl.n),
        {right, 
        split,
        exact hj.symm,
        rw eq_comm at hni,
        convert hni using 1,},
        have hmod := (game.remove_of_modify_symm p2 0 ⟨i, hi⟩ ⟨i, hi2⟩ (by refl) ho),
        have Hind := (H (game.remove G2 0 ⟨i, hi⟩) _ (game.remove G1 0 ⟨i, hi2⟩) hmod),
        swap,
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
          convert Hind using 2,
          ring,
        },
      },
      { have G1G2_1 : G2.f 0 = G1.f 0,
        rw eq_comm at hj,
        exact p2.hj 0 hj,
        simp only [G1G2_1],
        { have ho : 0 ≠ p2.j ∨ (0 = p2.j ∧ ((⟨i, hi⟩ : fin (length (G2.f 0))).val) ≠ p2.hl.n),
        {left, rw eq_comm at hj, exact hj,},
        have hmod := (game.remove_of_modify_symm p2 0 ⟨i, hi⟩ ⟨i, hi2⟩ (by refl) ho),
        have Hind := (H (game.remove G2 0 ⟨i, hi⟩) _ (game.remove G1 0 ⟨i, hi2⟩) hmod),
         swap,
          {rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
suffices : abs
            (abs (2 - game.value (game.remove G2 0 ⟨i, hi⟩)) -
             abs (2 - game.value (game.remove G1 0 ⟨i, hi2⟩))) ≤ d,
          { convert this using 2,
            rw [(show ((0 : fin 2).val : ℤ) = 0, by norm_cast), mul_zero, zero_add],
            ring,
          },
          apply le_trans (abs_abs_sub_abs_le _ _),
          convert Hind using 2,
          ring,
        },
        },

        },
    { -- i not < length G0
      
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
      rw sum_list2 at hiL_1,
      have hi_new : i - length (G2.f 0) < length (G2.f 1), 
      { rwa [nat.sub_lt_right_iff_lt_add hi, add_comm],
      },
      have h1length : length (G2.f 1) = length (G1.f 1),
            apply eq_list_lengths_of_modify p2,
      have hi_new2 : i - length (G2.f 0) < length (G1.f 1),
            rw ←h1length,
            exact hi_new,
      have hi_new2' : i - length (G1.f 0) < length (G1.f 1),
            convert hi_new2 using 2,
            symmetry,
            apply eq_list_lengths_of_modify p2,
      have h0length : length (G2.f 0) = length (G1.f 0),
            apply eq_list_lengths_of_modify p2,
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
          have nth_le_eq : nth_le (G2.f 1) (i - length (G2.f 0)) hi_new 
          = nth_le (G1.f 1) (i - length (G2.f 0)) hi_new2,
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
          rw nth_le_eq,
          suffices : abs (
            abs (4 - game.value (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩))
            - abs (4 - game.value (game.remove G1 1 ⟨i - length (G1.f 0), hi_new2'⟩))
          ) ≤ d, 
          { convert this using 2,
            rw (show (((1 : fin 2).val) : ℤ) = 1, by norm_cast),
            simp only [h0length],
            ring,
          },
          refine le_trans (abs_abs_sub_abs_le _ _) _,
          --have Hind := (H (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩) _ (game.remove G1 1 ⟨i - length (G1.f 0), _⟩) 
          --(game.remove_of_modify_symm p2 1 ⟨i - length (G2.f 0), hi_new⟩ ⟨i - length (G1.f 0), _⟩ _)),
          have ho : 1 ≠ p2.j ∨ (1 = p2.j ∧ ((⟨i - length (G2.f 0), hi_new⟩: fin (length (G2.f 1))).val) ≠ p2.hl.n),
        {right, 
        split,
        exact hj.symm,
        rw eq_comm at hni,
        convert hni using 1,},
        have hmod := (game.remove_of_modify_symm p2 1 ⟨i - length (G2.f 0), hi_new⟩ ⟨i - length (G1.f 0), _⟩ _ ho),
        have Hind := (H (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩) _ (game.remove G1 1 ⟨i - length (G1.f 0), _⟩) hmod),
          { convert Hind using 2,
            ring,
            exact hi_new2',
          },
          { rw game.size2_remove,
           rw hs,
           exact nat.add_sub_cancel n 1,
          },
          dsimp, rw h0length,
        },
      },
      { have G1G2_1 : G2.f 1 = G1.f 1,
        rw eq_comm at hj,
        exact p2.hj 1 hj,
        simp only [G1G2_1],
        suffices : abs (
            abs (4 - game.value (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩))
            - abs (4 - game.value (game.remove G1 1 ⟨i - length (G1.f 0), hi_new2'⟩))
          ) ≤ d, 
          { convert this using 2,
            rw (show (((1 : fin 2).val) : ℤ) = 1, by norm_cast),
            simp only [h0length],
            ring,
          },
          refine le_trans (abs_abs_sub_abs_le _ _) _,
         have ho : 1 ≠ p2.j ∨ (1 = p2.j ∧ ((⟨i - length (G2.f 0), hi_new⟩: fin (length (G2.f 1))).val) ≠ p2.hl.n),
        {left, rw eq_comm at hj, exact hj,},
        have hmod := (game.remove_of_modify_symm p2 1 ⟨i - length (G2.f 0), hi_new⟩ ⟨i - length (G1.f 0), _⟩ _ ho),
        have Hind := (H (game.remove G2 1 ⟨i - length (G2.f 0), hi_new⟩) _ (game.remove G1 1 ⟨i - length (G1.f 0), _⟩) hmod),
          { convert Hind using 2,
            ring,
            exact hi_new2',
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
end
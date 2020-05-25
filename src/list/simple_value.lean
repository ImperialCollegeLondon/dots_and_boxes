import tactic.linarith list.min.basic


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

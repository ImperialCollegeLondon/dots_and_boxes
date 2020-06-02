import tactic.linarith list.min.basic

-- tf = 2 if we are talking about chains and 4 otherwise

-- all games are assumed to consist only of loops or only of chains

/-- Let G be all chains or loops. If m is the length of a component of G, and
  vL = value of game G with that component removed, list.aux_fun this is the 
  value of G given that we're playing in that component -/
def list.aux_fun (m tf vL : ℤ) := m - tf + abs(tf - vL)


/--if two components M1, M2 differ by at most d in length 
  and v(G1;M1) = v(G2;M2), then the value given we are playing 
  in any of them differs by at most d-/
theorem list.aux_fun_L1 {m1 m2 tf vL d : ℤ} (hm : abs (m1 - m2) ≤ d) :
  abs(list.aux_fun m1 tf vL - list.aux_fun m2 tf vL) ≤ d :=
begin
  unfold list.aux_fun, finish, -- Lean can prove this by itself
end


/--if we have two games with a component of length m of the same
   type and the values of each game with such a component removed
   differ by at most d then the value given we are playing in such
   a component in any of them differs by at most d-/
theorem list.aux_fun_L2 {m tf vL1 vL2 d : ℤ} (hm : abs (vL1 - vL2) ≤ d) :
  abs(list.aux_fun m tf vL1 - list.aux_fun m tf vL2) ≤ d :=
begin
 unfold list.aux_fun, 
 rw sub_add_eq_sub_sub_swap, 
 /- the goal is : abs (m - tf + abs (tf - vL1) - abs (tf - vL2) - (m - tf)) ≤ d-/

/- As we are dealing with integers, this is equivalent to 
    abs (abs (tf - vL1) - abs (tf - vL2)) ≤ d -/
 rw add_comm,
 show abs (abs (tf + -vL1) + (m + -tf) + -abs (tf + -vL2) + -(m + -tf)) ≤ d,
 rw add_assoc,
 rw add_assoc, 
 rw add_comm (m + -tf), 
 rw add_assoc, 
 rw add_comm (-(m+-tf)),
 rw add_neg_self (m+-tf), 
 rw add_zero, 

 /- we want to solve the goal by using that by hm, abs(tf - vL1 - (tf - vL2)) ≤ d
    and by another lemma abs (abs (tf - vL1) - abs (tf - vL2)) ≤ abs(tf - vL1 - (tf - vL2))
    through transitivity of ≤ -/

 have Q: abs(tf - vL1 - (tf - vL2)) ≤ d, 
  {  rw ←  abs_neg, -- abs(tf - vL1 - (tf - vL2)) = abs(-(tf - vL1 - (tf - vL2)))
     convert hm, -- abs(-(tf - vL1 - (tf - vL2))) ≤ d is basically hm
     -- so what is left to prove for Q is that -(tf - vL1 - (tf - vL2)) = vL1 - vL2
     ring,},  -- using that ( ℤ, *, +) is a ring (so commutativity and associativity hold)

 have R: abs (abs (tf - vL1) - abs (tf - vL2)) ≤ abs ((tf - vL1) - (tf - vL2)),
  {exact abs_abs_sub_abs_le_abs_sub (tf - vL1) (tf - vL2)}, -- see misc_lemmas
 exact le_trans R Q, -- proven by Q, R and transitivity of ≤ 
end


/-- Value of all-chain or all-loop game L with n components
 given that we are opening the i'th component first-/
definition list.value_i (tf : ℤ) :
  ∀ (n : ℕ) (L : list ℤ) (i : fin n) (hL : L.length = n), ℤ
| (0) L i h := begin exfalso,  exact fin.elim0 i, end /- i.is_lt gives a contradiction (i < 0 is impossible)-/
| (d + 1) L i h := list.aux_fun (L.nth_le i.val (by rw h; exact i.is_lt)) tf (list.min' (list.of_fn $
    λ (j : fin d), list.value_i d (L.remove_nth i.val) j begin
      rw list.length_remove_nth L i.val _,
        rw h, simp,
      rw h, exact i.is_lt,
    end))


/-  The first case being a contradiction also makes sense for our definition.
     we cannot open a component first if the game is empty
     
     list.value_i tf n L i hL  is defined inductively on the number of components as 
     L.nth_le i.val _ - tf + abs ( tf - v ),
      where v is the minimum value of list.value_i (n - 1) (L.remove_nth i.val) j _over all j in fin (n - 1). 
      As we define he minimum element of the empty list to be zero, if our 'game' has only one component,
      (ie. n = 1) , we have list.value_i tf 1 L ⟨0,_⟩ hL = 
      L.nth_le 0 _ - tf + abs ( tf - 0 ), which is the length of the component, as it should be.
      (i = ⟨0,_⟩ is the only possibility as we must have i.val < n)
      So this recursion terminates.-/

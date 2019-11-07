import sle.basic_odd_loops
import data.multiset


/--Incrementing one component of a multiset of naturals by one-/
def multiset_one_comp_plus_one (A : multiset ℕ )(a : ℕ )(P : a ∈ A): multiset ℕ  :=
(a+1) :: (multiset.erase A a)

/--Decrementing one component of a multiset of naturals by one-/
def multiset_one_comp_minus_one (A : multiset ℕ )(a : ℕ )(P : a ∈ A): multiset ℕ  :=
(a-1) :: (multiset.erase A a)

/--increasing the length of one loop of a olsle by one-/
def one_loop_plus_one (G : olsle)(a : ℕ )(P : a ∈ G.loops): olsle:= 
{
  chains := (olsle.chains G),
  chains_are_long := G.chains_are_long,
  loops := multiset_one_comp_plus_one G.loops a P,
  loops_are_long := begin intros,have H1 : ∀ x ∈ G.loops, 4 ≤ x, by exact G.loops_are_long,
  unfold multiset_one_comp_plus_one at H, rw multiset.mem_cons at H, cases H, have H2 : 4 ≤ a, finish,rw H, 
  have H3 : a ≤ a + 1, by simp, exact le_trans H2 H3, 
  have H2 : x ∈ G.loops, by exact multiset.mem_of_mem_erase H, finish, end,
}

/--decreasing the length of one loop of a olsle by one-/
def one_loop_minus_one (G : olsle)(a : ℕ )(P : a ∈ G.loops)(P2 : 5 ≤ a): olsle:= 
{
  chains := (olsle.chains G),
  chains_are_long := G.chains_are_long,
  loops := multiset_one_comp_minus_one G.loops a P,
  loops_are_long := begin intros,have H1 : ∀ x ∈ G.loops, 4 ≤ x, by exact G.loops_are_long,
  unfold multiset_one_comp_minus_one at H, rw multiset.mem_cons at H, cases H, rw H, rw nat.le_sub_right_iff_add_le, finish, exact le_trans (by norm_num) P2 ,
  have H2 : x ∈ G.loops, by exact multiset.mem_of_mem_erase H, finish, end,
}




/--increasing the length of one chain of a olsle by one-/
def one_chain_plus_one (G : olsle)(a : ℕ )(P : a ∈ G.chains): olsle:= 
{
  chains := multiset_one_comp_plus_one G.chains a P,
  chains_are_long := begin intros,have H1 : ∀ x ∈ G.chains, 3 ≤ x, by exact G.chains_are_long,
  unfold multiset_one_comp_plus_one at H, rw multiset.mem_cons at H, cases H, have H2 : 3 ≤ a, finish,rw H, 
  have H3 : a ≤ a + 1, by simp, exact le_trans H2 H3, 
  have H2 : x ∈ G.chains, by exact multiset.mem_of_mem_erase H, finish, end,
  loops := (olsle.loops G),
  loops_are_long := G.loops_are_long
}

/--decreasing the length of one Chain of a olsle by one-/
def one_chain_minus_one (G : olsle)(a : ℕ )(P : a ∈ G.chains)(P2 : 4 ≤ a): olsle:= 
{
  chains := multiset_one_comp_minus_one G.chains a P,
  chains_are_long := begin intros,have H1 : ∀ x ∈ G.chains, 3 ≤ x, by exact G.chains_are_long,
  unfold multiset_one_comp_minus_one at H,  rw multiset.mem_cons at H, cases H, rw H, rw nat.le_sub_right_iff_add_le, finish, exact le_trans (by norm_num) P2 ,
  have H2 : x ∈ G.chains, by exact multiset.mem_of_mem_erase H, finish, end,
  
  loops := (olsle.loops G),
  loops_are_long := G.loops_are_long
}




/--increasing the length of one loop of a olsle by one changes the value of the game by one-/
theorem value_loop_plus_one (G : olsle)(a : ℕ )(P : a ∈ G.loops) (G' : olsle) (G' = (one_loop_plus_one G a P)) :
olvalue G' = olvalue G + 1 ∨ olvalue G' = olvalue G - 1 := 
begin 
sorry
end
/--decreasing the length of one loop of a olsle by one changes the value of the game by one-/
theorem value_loop_minus_one (G : olsle)(a : ℕ )(P : a ∈ G.loops) (P2 : 5 ≤ a) (G' : olsle) (G' = (one_loop_minus_one G a P P2)) :
olvalue G' = olvalue G + 1 ∨ olvalue G' = olvalue G - 1 := 
begin 
sorry
end

/--increasing the length of one chain of a olsle by one changes the value of the game by one-/
theorem value_chain_plus_one (G : olsle)(a : ℕ )(P : a ∈ G.chains) (G' : olsle) (G' = (one_chain_plus_one G a P)) :
olvalue G' = olvalue G + 1 ∨ olvalue G' = olvalue G - 1 := 
begin 
sorry
end

/--decreasing the length of one chain of a olsle by one changes the value of the game by one-/
theorem value_chain_minus_one (G : olsle)(a : ℕ )(P : a ∈ G.chains) (P2 : 4 ≤ a)(G' : olsle) (G' = (one_chain_minus_one G a P P2)) :
olvalue G' = olvalue G + 1 ∨ olvalue G' = olvalue G - 1 := 
begin 
sorry
end
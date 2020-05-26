import game.basic
import list.modify.basic
import tactic.fin_cases

open list

namespace game

/--Two games that are equal except one entry in one sublist of components differs by at most d-/
structure modify {n : ℕ} (G1 G2 : game n) (d : ℤ) :=
(j : fin n)
(hj : ∀ i : fin n, i ≠ j → G1.f i = G2.f i)
(hl : list.modify (G1.f j) (G2.f j) d)



/--For two games that are equal except one pair of components of the same type differs 
by at most d, both games have the same number of components of each type-/
lemma eq_list_lengths_of_modify {n : ℕ} {G1 G2 : game n} {d : ℤ} (h : modify G1 G2 d):
∀ (i : fin n), length (G1.f i) = length (G2.f i) :=
begin
cases h with j heq modi, 
intro i,
by_cases p1 : i ≠ j,
rw heq i p1,
push_neg at p1,
rw ← p1 at modi,
exact eq_size_of_modify_list modi,
end

end game

open game 

/--if G1 is a version of G2 modified in one component by at most d, 
then G2 is a version of G1 modified in one component by at most d-/
def modify.symm {G1 G2 : game 2} {d : ℤ} 
(m : modify G1 G2 d) : modify G2 G1 d :=
{ j := m.j,
  hj := begin intros i h, rw eq_comm, exact m.hj i h, end,
  hl := begin apply list.modify.symm, exact m.hl, end,
}


/--games modified in one comonent have the same size-/
theorem eq_size_of_modify {G1 G2 : game 2} {d : ℤ} (h : game.modify G1 G2 d) : G1.size2 = G2.size2 :=
begin
  cases h with j hj hjm, 
  unfold size2,
  fin_cases j,
  { have h0 := eq_size_of_modify_list hjm, 
    change length (G1.f 0) = length (G2.f 0) at h0,
    have h1 : G1.f 1 = G2.f 1,
      exact hj ⟨1, dec_trivial⟩ dec_trivial,
    rw [h0, h1],
  },
  {
    have h0 := eq_size_of_modify_list hjm, 
    change length (G1.f 1) = length (G2.f 1) at h0,
    have h1 : G1.f 0 = G2.f 0,
      exact hj ⟨0, dec_trivial⟩ dec_trivial,
    rw [h0, h1],
  }
end


/--If you remove some component that is not the modified one from
both modified games, you get a modified game-/
def game.remove_of_modify {G1 G2 : game 2} {d : ℤ }
(p : modify G1 G2 d) (j : fin 2) (i1 : fin (G1.f j).length)
(i2 : fin (G2.f j).length) (hi : i1.val = i2.val)(h : j ≠ p.j ∨ (j = p.j ∧ i1.val ≠ p.hl.n)): 
modify (G1.remove j i1) (G2.remove j i2) d :=
begin

split,
swap 3, {exact p.j},
{intros x x_neq,
unfold game.remove,
dsimp,
split_ifs,
{rw hi,
rw h_1 at x_neq,
rw p.hj j x_neq},
{ exact p.hj x x_neq,},
  },
{
  unfold game.remove,dsimp,
  split_ifs,
  {rw ← hi, 
  rw eq_comm at h_1,
  simp only [h_1],
  {have pj2 : j = p.j ∧ i1.val ≠ p.hl.n,
   finish,
  exact list.modify_remove_nth p.hl i1.val pj2.right,},
  },
  exact p.hl,
},

end


/--game.remove_of_modify with roles of G1 and G2 switched-/
def game.remove_of_modify_symm{G1 G2 : game 2} {d : ℤ }
(p : modify G1 G2 d) (j : fin 2) (i1 : fin (G1.f j).length)
(i2 : fin (G2.f j).length) (hi : i1.val = i2.val)(h : j ≠ p.j ∨ (j = p.j ∧ i1.val ≠ p.hl.n)): 
modify (G2.remove j i2) (G1.remove j i1) d := 
by exact modify.symm (game.remove_of_modify p j i1 i2 hi h)


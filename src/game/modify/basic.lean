import game.basic
import list.modify.basic
import tactic.fin_cases

open list

namespace game

/--Two games that are equal except one entry in one sublist of components differs by at most d-/
structure modify {n : ℕ} (G1 G2 : game n) (d : ℤ) :=
(j : fin n)  -- kind of the component they differ in (there are n kinds of componenents)
(hj : ∀ i : fin n, i ≠ j → G1.f i = G2.f i) /- if we are NOT looking at the kind of component they differ in,
                                               the lists of such components in both games is the same-/
(hl : list.modify (G1.f j) (G2.f j) d) /- if we are looking at the kind of component they differ in,
                                               the lists of such components in both games differ 
                                               in one component by at most d-/



/--For two games that are equal except one pair of components of the same type differs 
by at most d, both games have the same number of components of each type-/
lemma eq_list_lengths_of_modify {n : ℕ} {G1 G2 : game n} {d : ℤ} (h : modify G1 G2 d):
∀ (i : fin n), length (G1.f i) = length (G2.f i) :=
begin
intro i,
/- either the games differ in a component of kind i or they do differ somewhere else-/
by_cases p1 : i ≠ h.j,
  /- if they do not differ in a component of kind i, then by h.hj the 
     lists are the same, hence their lengths as well-/
  {rw h.hj i p1},
  /- if they do differ in a component of kind i, then by h.hl the 
     lists are modified lists, hence their lengths are the same
     by a lemma in list.modify.basic-/
  {push_neg at p1,
  rw p1,
  exact eq_size_of_modify_list h.hl},
end

end game

open game 

/--if G1 is a version of G2 modified in one component by at most d, 
then G2 is a version of G1 modified in one component by at most d-/
def modify.symm {G1 G2 : game 2} {d : ℤ} 
(m : modify G1 G2 d) : modify G2 G1 d :=
{ j := m.j,-- they still differ in the same components
  hj := begin intros i h, rw eq_comm, exact m.hj i h, end, --follows from symmetry of equality in m.hj
  hl := begin apply list.modify.symm, exact m.hl, end, -- follows from symmetry of list.modify
}


/--games modified in one comonent have the same size-/
theorem eq_size_of_modify {G1 G2 : game 2} {d : ℤ} (h : game.modify G1 G2 d) : G1.size2 = G2.size2 :=
begin
  cases h with j hj hl, --split h into its fields
  unfold size2, -- size Gn = length (Gn.f 0) + length (Gn.f 1) for n = 1, 2
  fin_cases j, -- split into cases corresponding to possible values of j in fin 2

  /- in both cases we prove the number of chains are the same (h0)
     and the number of looops are the same (h1)  
     (or the lists are the same, which implies the above)
     then clearly the sizes of the games are the same-/

  -- j = ⟨0,_⟩ 
  { have h0 := eq_size_of_modify_list hl, -- length (G1.f ⟨0, _⟩) = length (G2.f ⟨0, _⟩)
    change length (G1.f 0) = length (G2.f 0) at h0,
    have h1 : G1.f 1 = G2.f 1, 
      exact hj ⟨1, dec_trivial⟩ dec_trivial, -- as we do not modify a loop, by hj
    rw [h0, h1],
  },
  -- j = ⟨1,_⟩ 
  { have h0 : G1.f 0 = G2.f 0,
      exact hj ⟨0, dec_trivial⟩ dec_trivial, -- as we do not modify a chain, by hj
    have h1 := eq_size_of_modify_list hl, -- length (G1.f ⟨1, _⟩) = length (G2.f ⟨1, _⟩)
    change length (G1.f 1) = length (G2.f 1) at h1,
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
  split, -- split goal into its fields

    -- FIELD j
    swap 3, {exact p.j}, -- they still differ in the same kind of component

    -- FIELD hj
    {intros x x_neq, -- say we are looking at a kind x of component, that is not p.j
    unfold game.remove,
    show dite (x = j) (λ (h : x = j), remove_nth (G1.f j) (i1.val)) (λ (h : ¬x = j), G1.f x) =
        dite (x = j) (λ (h : x = j), remove_nth (G2.f j) (i2.val)) (λ (h : ¬x = j), G2.f x),
    split_ifs with ite, -- either x = j or ¬ (x = j)

      /- in both cases by h.hj, G1.f x and G2.f x are the same because of x_neq-/
      
      -- if-case (named ite) : x = j 
      {rw hi, -- i1.val and i2.val are the same
      rw ite at x_neq,
      rw p.hj j x_neq},
      -- else-case (named ite) : ¬ (x = j)
      { exact p.hj x x_neq,},
        },


    -- FIELD hl
    {
      unfold game.remove,
      -- in the following, list.modify is meant
      show modify (dite (p.j = j) (λ (h : p.j = j), remove_nth (G1.f j) (i1.val)) (λ (h : ¬p.j = j), G1.f (p.j)))
          (dite (p.j = j) (λ (h : p.j = j), remove_nth (G2.f j) (i2.val)) (λ (h : ¬p.j = j), G2.f (p.j))) d,
      split_ifs with ite, -- either p.j = j or ¬ (p.j = j)
        -- if-case (named ite) : p.j = j
        {rw ← hi, 
        rw eq_comm at ite,
        simp only [ite],
        have pj2 : j = p.j ∧ i1.val ≠ p.hl.n, --this is true because of h and ite
          {finish},
        /- hence i1.val ≠ p.hl.n, which together with p.hl is all we need
           to be able to use list.modify_remove_nth (see list.modify.basic)-/
        exact list.modify_remove_nth p.hl i1.val pj2.right,},
        -- else-case (named ite) : ¬ (p.j = j) 
        {exact p.hl}, -- this is exactly what p.hl says
    },

end


/--game.remove_of_modify with roles of G1 and G2 switched-/
def game.remove_of_modify_symm{G1 G2 : game 2} {d : ℤ }
(p : modify G1 G2 d) (j : fin 2) (i1 : fin (G1.f j).length)
(i2 : fin (G2.f j).length) (hi : i1.val = i2.val)(h : j ≠ p.j ∨ (j = p.j ∧ i1.val ≠ p.hl.n)): 
modify (G2.remove j i2) (G1.remove j i1) d := 
by exact modify.symm (game.remove_of_modify p j i1 i2 hi h)


import data.list.basic tactic.linarith
import tactic.omega tactic.apply
import list.lemmas.long_lemmas
import tactic.fin_cases

open list


/-- abstract game with n types of components, 
each type represented by a list -/
structure game (n : ℕ) :=
(f : fin n → list ℤ) /- a function from types of components to the
                        corresponding list of lengths of these components-/

namespace game

/--extensionality of a game-/
@[ext] theorem ext {n : ℕ} (G1 G2 : game n) : 
(∀ (i : ℕ) (hi : i < n), G1.f ⟨i, hi⟩ = G2.f ⟨i, hi⟩) → G1 = G2 :=
begin
  intro h,
  cases G1, -- unfold field of G1
  cases G2, -- unfold field of G2
  rw mk.inj_eq, -- chages the goal to basically G1.f = G2.f
  funext j, -- the functions are the same if for all j in fin n, G1.f j = G2.f j
  cases j with i hi, -- split j ino its fields (which are also i and hi as above)
  exact h i hi, -- now this is true by our hypothesis
end

/--the empty game / completed game-/
def zero (n : ℕ): game n:=
{
  f := λ (i : fin n), nil /- all kinds of components have corresponding 
                             list of lengths of these components nil -/
}



/--the size of a game with only chains and loops-/
def size2 (G : game 2) : ℕ := 
length (G.f (0:fin 2)) + length (G.f (1:fin 2)) 



/--The number of components of a game-/
def size {n : ℕ} (G : game n) : ℕ := 
list.sum (list.of_fn (λ i, (G.f i).length))

/--For a game with only chains and loops the definitions 
of the size, size and size2, are equivalent-/
theorem size_eq_size2 (G : game 2) : G.size = G.size2 :=
begin
  /- size G is here definitionally equal to 
  (0 + length (G.f (0:fin 2))) + length (G.f (1:fin 2)),
  so this just amounts to the addition of 0 cancelling -/
  show (0 + _) + _ = _ + _,
  rw zero_add,
  refl,
end

/--The size2 of the empty game is 0-/
lemma size2_zero : (zero 2).size2 = 0 := rfl

/--If size2 of a game is 0, it is the empty game-/
lemma eq_zero_of_size2_zero (G : game 2) : G.size2 = 0 → G = zero 2 :=
begin 
  intro h,
  replace h := nat.eq_zero_of_add_eq_zero h, /- replace (basically) length (G.f 0) + length (G.f 1) = 0 
                                                by length (G.f 0) = 0 ∧ length (G.f 1) = 0 -/
  unfold zero,
  cases h with h1 h2, 
  rw length_eq_zero at h1 h2, -- length (G.f j) = 0 ↔ G.f j = nil (j = 0, 1)
  cases G, --replace G by its field
  apply game.ext,
  -- from here on we basically need to prove G.f 0 and G.f 1 are both empty
  intros i hi,
  set i0 : fin 2 := ⟨i, hi⟩,
  fin_cases i0, -- either i0 is ⟨0, _⟩ or ⟨1, _⟩ as it is of type fin 2
    -- i0 = ⟨0, _⟩ (so h1 proves the goal)
    {rw h,
    exact h1},
    -- i0 = ⟨1, _⟩ (so h2 proves the goal)
    { rw h,
      exact h2},
end


/--used to create a recurser on size2-/
def rec_on_size2' (C : game 2→ Sort*) :
(∀ G : game 2, G.size2 = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game 2, G.size2 = m → C G := λ z ih n, nat.rec z ih n


universe u

/--recursor on size2-/
def rec_on_size2 {C : game 2 → Sort u} :
C (game.zero 2) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ G : game 2, C G :=
λ z ih G, @game.rec_on_size2' C (λ H hH, (by rwa eq_zero_of_size2_zero _ hH : C H)) ih (G.size2) _ rfl



/-- Remove i'th element of j'th component list of G -/
def remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) : game 2 :=
{f := λ k, if h : k = j then list.remove_nth (G.f j) i.val else (G.f k)}


/--The size of a game with one component removed-/
lemma size2_remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) :
  (G.remove j i).size2 = G.size2 - 1 :=
begin
  fin_cases j, -- split into cases for all possible values of j 
  -- j = ⟨0, _⟩
  { show _ + _ = _ + _ - 1, -- we basically use the definition of size2 here
    unfold game.remove,
    dsimp,

    /- uses definitions to change the goal to :
       length
        (dite (0 = ⟨0, _⟩) (λ (h : 0 = ⟨0, _⟩), remove_nth (G.f ⟨0, _⟩) (i.val))
           (λ (h : ¬0 = ⟨0, _⟩), G.f 0)) +
       length
        (dite (1 = ⟨0, _⟩) (λ (h : 1 = ⟨0, _⟩), remove_nth (G.f ⟨0, _⟩) (i.val))
           (λ (h : ¬1 = ⟨0, _⟩), G.f 1)) =
       length (G.f 0) + length (G.f 1) - 1-/

    split_ifs with H1 H2 H2, -- split into cases based on the if-conditions
    -- H1 : 0 = ⟨0, _⟩, H2 : 1 = ⟨0, _⟩
    { cases H2}, -- H2 is clearly false
    -- H1 : 0 = ⟨0, _⟩, H2 : ¬ (1 = ⟨0, _⟩)
    { rw length_remove_nth _ _ i.is_lt, /- as i < length (G.f ⟨0, _⟩), removing index 
                                           i.val decreases the length by 1 -/
      show length (G.f 0) - 1 + length (G.f 1) = 
        length (G.f 0) + length (G.f 1) - 1,
      have i2 := i.is_lt, -- i2 is i.val < length (G.f ⟨0, _⟩)  (so we can change and then use this)
      change i.val < length (G.f 0) at i2,
      /- we replace every occurence of length (G.f 0) by a natural number
         so we can treat it as such -/
      generalize hm : length (G.f 0) = m,
      rw hm at i2,
      -- if that length is 0, we get a conradiction as i2 is in ℕ and less than 0
      cases m with m,
        -- m = 0
        cases i2,
      -- nat.succ m
      generalize hm2 : length (G.f 1) = m2,
      /- because nat.succ m ≥ 1 , the goal, nat.succ m - 1 + m2 = nat.succ m + m2 - 1,
        is just a matter of changing the order. Lean can do this with omega-/
      clear i2 i hm hm2 G,
      omega},
     -- H1 : ¬ (0 = ⟨0, _⟩), H2 : 1 = ⟨0, _⟩
    { cases H2}, -- H2 is clearly false
    -- H1 : ¬ (0 = ⟨0, _⟩), H2 : ¬ (1 = ⟨0, _⟩)
    { exfalso, apply H1, refl}, -- H1 is clearly false (H1 is 0 = ⟨0, _⟩ → false)
  },

  -- j = ⟨1, _⟩
  { show _ + _ = _ + _ - 1,
    unfold game.remove,
    dsimp,

    /- uses definitions to change the goal to :
       length
           (dite (0 = ⟨1, _⟩) (λ (h : 0 = ⟨1, _⟩), remove_nth (G.f ⟨1, _⟩) (i.val))
           (λ (h : ¬0 = ⟨1, _⟩), G.f 0)) +
       length
           (dite (1 = ⟨1, _⟩) (λ (h : 1 = ⟨1, _⟩), remove_nth (G.f ⟨1, _⟩) (i.val))
           (λ (h : ¬1 = ⟨1, _⟩), G.f 1)) =
       length (G.f 0) + length (G.f 1) - 1 -/

    split_ifs with H1 H2 H2,
    -- H1 : 0 = ⟨1, _⟩, H2 : 1 = ⟨1, _⟩
    { cases H1}, -- H1 is clearly false
    -- H1 : 0 = ⟨1, _⟩, H2 : ¬ (1 = ⟨1, _⟩)
    { cases H1}, -- H1 is clearly false
    -- H1 : ¬ (0 = ⟨1, _⟩), H2 : 1 = ⟨1, _⟩  (similar to above)
    { rw length_remove_nth _ _ i.is_lt,
      show length (G.f 0) + (length (G.f 1) - 1) = 
        length (G.f 0) + length (G.f 1) - 1,
      have i2 := i.is_lt,
      change i.val < length (G.f 1) at i2,
      generalize hm : length (G.f 1) = m, rw hm at i2,
      generalize hm2 : length (G.f 0) = m2,
      cases m with m,
        cases i2,
      clear i2 i hm hm2 G,
      omega},
    -- H1 : ¬ (0 = ⟨1, _⟩), H2 : ¬ (1 = ⟨1, _⟩)
    { exfalso, apply H2, refl} -- H2 gives a contradiction (H2 is 1 = ⟨1, _⟩ → false)
  }
end


end game



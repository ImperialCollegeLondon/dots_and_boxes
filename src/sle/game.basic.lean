import data.list.basic tactic.linarith
import tactic.omega tactic.apply
import sle.lemmas
import tactic.fin_cases

open list


/-- abstract game with n types of list as components -/
structure game (n : ℕ) :=
(f : fin n → list ℤ)

namespace game
@[ext] def ext {n : ℕ} (G1 G2 : game n) : (∀ (i : ℕ) (hi : i < n), G1.f ⟨i, hi⟩ = G2.f ⟨i, hi⟩) → G1 = G2 :=
begin
  intro h,
  cases G1, cases G2,
  rw mk.inj_eq,
  funext j,
  cases j with i hi,
  apply h,
end

/--the empty game / completed game-/
def zero (n : ℕ): game n:=
{
  f := λ (i : fin n), nil
}



/--the size of a game with only chains and loops-/
def size2 (G : game 2) : ℕ := 
length (G.f (0:fin 2)) + length (G.f (1:fin 2)) 


def rec_on_size2' (C : game 2→ Sort*) :
(∀ G : game 2, G.size2 = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game 2, G.size2 = m → C G := λ z ih n, nat.rec z ih n


/--The number of components of a game-/
def size {n : ℕ} (G : game n) : ℕ := 
list.sum (list.of_fn (λ i, (G.f i).length))

/--For a game with only chains and loops the definitions 
of the size, size and size2, are equivalent-/
theorem size_eq_size2 (G : game 2) : G.size = G.size2 :=
begin
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
  replace h := nat.eq_zero_of_add_eq_zero h,
  unfold zero,
  cases h with h1 h2,
  rw length_eq_zero at h1 h2,
  cases G,
  apply game.ext,
  intros i hi,
  set i0 : fin 2 := ⟨i, hi⟩,
  fin_cases i0; rw h,
    exact h1,
    exact h2,
end

universe u
--@[elab_as_eliminator]
def rec_on_size2 {C : game 2 → Sort u} :
C (game.zero 2) → (∀ n : ℕ, 
  (∀ G : game 2, G.size2 = n → C G) → (∀ G : game 2, G.size2 = n + 1 → C G)) →
  ∀ G : game 2, C G :=
λ z ih G, @game.rec_on_size2' C (λ H hH, (by rwa eq_zero_of_size2_zero _ hH : C H)) ih (G.size2) _ rfl



/-- Remove i'th element of j'th component of G -/
def remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) : game 2 :=
{f := λ k, if h : k = j then list.remove_nth (G.f j) i.val else (G.f k)}

lemma size2_remove (G : game 2) (j : fin 2) (i : fin (G.f j).length) :
  (G.remove j i).size2 = G.size2 - 1 :=
begin
  fin_cases j,
  { show _ + _ = _ + _ - 1,
    unfold game.remove,
    dsimp,
    split_ifs,
    { cases h_1},
    { rw length_remove_nth _ _ i.is_lt, 
      show length (G.f 0) - 1 + length (G.f 1) = 
        length (G.f 0) + length (G.f 1) - 1,
      have i2 := i.is_lt,
      change i.val < length (G.f 0) at i2,
      generalize hm : length (G.f 0) = m,
      rw hm at i2,
      cases m with m,
        cases i2,
      generalize hm2 : length (G.f 1) = m2,
      clear i2 i hm hm2 G,
      omega},
    { cases h_1},
    { exfalso, apply h, refl},
  },
  { show _ + _ = _ + _ - 1,
    unfold game.remove,
    dsimp,
    split_ifs,
    { cases h},
    { cases h},
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
    { exfalso, apply h_1, refl}
  }
end


end game
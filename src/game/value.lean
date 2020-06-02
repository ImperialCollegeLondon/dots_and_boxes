import game.basic
import list.min.basic

open list
open game


/--the value of a non-empty game consisting of loops and chains-/
def game.value : game 2 → ℤ := @game.rec_on_size2 (λ G, ℤ) (0 : ℤ) $ λ n hn G hG,
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
      hn (G.remove j i) (by rw [game.size2_remove, hG, nat.add_sub_cancel])) --last bracket proves size2 (remove G j i) = n
  ))
  begin
    /- we need to prove list.bind [0, 1]
      (λ (j : fin 2),
         of_fn
           (λ (i : fin (length (G.f j))),
              nth_le (G.f j) (i.val) _ - (2 * ↑(j.val) + 2) + abs (2 * ↑(j.val) + 2 - hn (remove G j i) _))) ≠
    nil
      for list.min  (as it is not defined for empty lists-/
    intro h, -- a ≠ b  is the same as (a = b) → false so h is ... = nil

    /- we simplify h to sum [length (G.f 0), length (G.f 1)] = 0-/
    rw [←list.length_eq_zero, list.length_bind] at h,
    dsimp at h,
    rw [list.length_of_fn, list.length_of_fn] at h,

    change size G = 0 at h,
    -- now this cannot be true as size G = n + 1 by one of our assumptions
    rw [size_eq_size2, hG] at h,
    revert h, exact dec_trivial,
  end

  /- Note (2 * j.val + 2) is 2 if j corresponds to chains (j.val = 0) 
     and 4 if j corresponds to loops (j.val = 1)
     
     The value was defined recursively on the number of components using our recursor
     from game.basic-/


/--equivalence to a simpler definition given the size of the game-/
theorem game.value_def (G : game 2) (n : ℕ) (hG : G.size2 = nat.succ n):
  game.value G =
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
  game.value (G.remove j i))))
  begin -- for list.min. see proof above
    intro h,
    rw [←list.length_eq_zero, list.length_bind] at h,
    dsimp at h,
    rw [list.length_of_fn, list.length_of_fn] at h,
    change size G = 0 at h,
    rw [size_eq_size2, hG] at h,
    revert h, exact dec_trivial,
  end
:=
begin
  unfold game.value,
  unfold game.rec_on_size2,
  unfold game.rec_on_size2',
  simp only [hG],
  congr', --can prove the lists are the same which then implies the minimums are

  /-reduce outrageously long goal-/
  ext i n0 n1, --apply extensionality lemmas
  congr',
  ext j, --apply extensionality lemmas
  congr', /- goal is n = size2 (remove G i j), which implies the previous one
             (goal was of form g(n) = g (size2 (remove G i j)) for some function g)-/

  rw game.size2_remove, -- see game.basic
  rw hG,
  exact (nat.add_sub_cancel n 1).symm, -- as nat.succ n is defined as n + 1, +1 and -1 cancel
end


import game.basic
import list.min.basic

open list
open game



def game.value : game 2 → ℤ := @game.rec_on_size2 (λ G, ℤ) (0 : ℤ) $ λ n hn G hG,
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
      hn (G.remove j i) (by rw [game.size2_remove, hG, nat.add_sub_cancel])) 
  ))
  begin
    intro h,
    rw [←list.length_eq_zero, list.length_bind] at h,
    dsimp at h,
    rw [list.length_of_fn, list.length_of_fn] at h,
    change size G = 0 at h,
    rw [size_eq_size2, hG] at h,
    revert h, exact dec_trivial,
  end

theorem game.value_def (G : game 2) (n : ℕ) (hG : G.size2 = nat.succ n):
  game.value G =
  list.min (list.bind [(0 : fin 2), (1 : fin 2)] (λ j, 
  list.of_fn $ λ (i : fin (G.f j).length), 
      (G.f j).nth_le i.val i.is_lt - (2 * j.val + 2) + abs (2 * j.val + 2 - 
  game.value (G.remove j i))))
  begin
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
  congr',
  ext i n0 n1,
  congr',
  ext j,
  congr',
  rw game.size2_remove,
  rw hG,
  exact (nat.add_sub_cancel n 1).symm
end

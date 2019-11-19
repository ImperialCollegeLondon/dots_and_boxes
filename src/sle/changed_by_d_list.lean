import data.list.basic

open list

-- changing one element of a list by at most d

structure list.modify (A : list ℤ) (B : list ℤ) (d : ℕ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : int.nat_abs (A.nth_le n ha - B.nth_le n hb) ≤ d)

def list.modify.symm (A B : list ℤ) (d : ℕ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  bound := by rw [←neg_sub, int.nat_abs_neg]; exact m.bound
}

structure game :=
(C : list ℤ) (L : list ℤ)

inductive game.modify (G1 G2 : game) (d : ℕ)
| modifyc : list.modify G1.C G2.C d → (G1.L = G2.L) → game.modify
| modifyl : list.modify G1.L G2.L d → (G1.C = G2.C) → game.modify

def game.size (G : game) : ℕ := list.length G.C + list.length G.L

def list.min {X : Type*} [decidable_linear_order X] :
Π (L : list X), (L ≠ []) → X
| ([]) hL := false.elim $ hL rfl
| (x :: []) hL := x
| (x :: y :: L) _ := min x (list.min (y :: L) dec_trivial)

--def aux_fn (L : list ℤ) : fin (L.length) → ℤ :=
--λ i, i.val - 2 +int.nat_abs (value)

@[elab_as_eliminator]
def list.rec_on_length {X : Type*} {C : list X → Sort*} :
C [] → (∀ n : ℕ,
  (∀ L : list X, L.length = n → C L) → (∀ L : list X, L.length = n + 1 → C L)) →
  ∀ L : list X, C L := sorry

def chain_value : list ℤ → ℤ := list.rec_on_length 0 $
λ n H (L : list ℤ) hL, list.min
(list.of_fn $ λ (i : fin (n + 1)), (L.nth_le i.val $ hL.symm ▸ i.2) - 2 + (2 - H (L.remove_nth i.val) begin
  sorry -- removing elt from a list decreases length by 1
end)
)
begin
  intro h,
  have h2 : length(@list.nil ℤ) = 0,
    simp,
  rw ←h at h2,
  rw list.length_of_fn at h2,
  cases h2,
end

/- todo

1) list.rec_on_length (KB to do)
2) fill in sorry for chain_value
3) write loop_value (change two 2's to 4's)
4) write game_value : list ℤ → list ℤ → ℤ -- nice challenge!
5) Finally prove a theorem about game_value (maybe next week?)

-/

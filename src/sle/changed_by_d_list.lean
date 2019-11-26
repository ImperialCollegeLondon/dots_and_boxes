import data.list.basic tactic.linarith
import tactic.omega

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

namespace game
--extensionaliti changes in new mathlib
@[extensionality] def ext (G1 G2 : game) : G1 = G2 ↔ G1.C = G2.C ∧ G1.L = G2.L :=
by cases G1; cases G2; simp

-- for use later, in the MITM proof
inductive modify (G1 G2 : game) (d : ℕ)
| modifyc : list.modify G1.C G2.C d → (G1.L = G2.L) → modify
| modifyl : list.modify G1.L G2.L d → (G1.C = G2.C) → modify

def size (G : game) : ℕ := list.length G.C + list.length G.L

def zero : game := ⟨[], []⟩

lemma size_zero : zero.size = 0 := rfl

lemma eq_zero_of_size_zero {G : game} : G.size = 0 → G = zero :=
begin
  intro h,
  replace h := nat.eq_zero_of_add_eq_zero h,
  cases h with h1 h2,
  rw length_eq_zero at h1 h2,
  cases G, cases h1, cases h2, refl,
end

def list.min {X : Type*} [decidable_linear_order X] :
Π (L : list X), (L ≠ []) → X
| ([]) hL := false.elim $ hL rfl
| (x :: []) hL := x
| (x :: y :: L) _ := min x (list.min (y :: L) dec_trivial)

def game.rec_on_size' (C : game → Sort*) :
(∀ G : game, G.size = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game, G.size = m → C G := λ z ih n, nat.rec z ih n

universe u
--@[elab_as_eliminator]
def game.rec_on_size {C : game → Sort u} :
C zero → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ G : game, C G :=
λ z ih G, @game.rec_on_size' C (λ H hH, (by rwa eq_zero_of_size_zero hH : C H)) ih (G.size) _ rfl




def game.value : game → ℤ := @game.rec_on_size (λ G, ℤ) (0 : ℤ) $ λ n hn G hG,
  list.min 
    ((list.of_fn $ λ (i : fin G.C.length),
    G.C.nth_le i.val i.is_lt - 2 + abs (2 - hn {C := G.C.remove_nth i.val, L := G.L} begin
      unfold size, unfold size at hG, cases G,  rw remove_nth_eq_nth_tail,
      rw modify_nth_tail_eq_take_drop, show length (take (i.val) G_C ++ tail (drop (i.val) G_C)) + length G_L = n,
      rw list.length_append, rw length_take, rw length_tail, rw length_drop, 
      cases i with hi hj, show min hi (length G_C) + (length G_C - hi - 1) + length G_L = n,
      rw min_eq_left(le_of_lt hj), dsimp at hj, dsimp at hG, generalize hc:length G_C = c, rw hc at *,
       generalize hl:length G_L = l, rw hl at *,clear hc, clear G_C,clear hl G_L hn ,  omega, 
       refl, 
      
    end)) ++ (list.of_fn $ λ (i : fin G.L.length),
    G.L.nth_le i.val i.is_lt - 4 + abs (4 - hn {C := G.C, L := G.L.remove_nth i.val} begin
     unfold size, unfold size at hG, cases G,  rw remove_nth_eq_nth_tail,
      rw modify_nth_tail_eq_take_drop, show length G_C + length (take (i.val) G_L ++ tail (drop (i.val) G_L)) = n,
      rw list.length_append, rw length_take, rw length_tail, rw length_drop, 
      cases i with hi hj, show length G_C + (min hi (length G_L) + (length G_L - hi - 1)) = n, 
      rw min_eq_left(le_of_lt hj), dsimp at hj, dsimp at hG, generalize hc:length G_C = c, rw hc at *,
       generalize hl:length G_L = l, rw hl at *,clear hc, clear G_C,clear hl G_L hn ,  omega, refl, 
    end))) 
    begin
      apply ne_nil_of_length_pos, suffices : 0 < length (G.C) + length (G.L),simpa using this, unfold size at hG, rw hG, simp,
    end


/- todo

1) Fill in sorrys (first two shouldn't be hard, third might be more of a challenge, but I am pretty
sure I can do it)
2) Prove that if `h : game.modify G1 G2 d` then int.nat_abs(G1.value - G2.value) <= d by induction on size

-/
end game

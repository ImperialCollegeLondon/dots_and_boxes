import sle.basic

structure yasle :=
(chains : list ℕ)
(chains_are_long : ∀ x ∈ chains, 3 ≤ x)
(chains_sorted : list.sorted (nat.lt : ℕ → ℕ → Prop) chains)
(loops : list ℕ)
(loops_are_long_and_even : ∀ x ∈ loops, 4 ≤ x ∧ 2 ∣ x)
(loops_sorted : list.sorted (nat.lt) loops)

-- idea: compute *once* v(C-first x entries, L-first n-x entries) for 0<=x<=n,
-- looping through n

open nat list

-- val_aux n C L c l means values of the subgame of (C,L) of size n
-- consisting of the last c chains and the last l loops.
def val_aux : Π (n : ℕ), Π (C :list ℕ), Π (L : list ℕ), Π c : ℕ, Π l : ℕ , c + l = n →
  c ≤ C.length → l ≤ L.length → ℕ
| 0 C L 0 0 rfl _ _ := 0
| 0 C L _ (succ s) h _ _ := by cases h
| (succ n) nil nil c l h hc hl := false.elim begin
  cases hc, cases hl, cases h,
end
| (succ n) (a :: C) nil 0 l h hc hl := false.elim begin
  cases hl, cases h,
end
| (succ n) (a :: C) L (succ c) 0 h hc hl := a - 2 + int.nat_abs (2 - val_aux n C L c 0 begin
  exact succ_inj h,
end begin
 exact pred_le_iff.mpr hc
end hl)
| (succ n) nil (b :: L) c 0 h hc hl := false.elim begin
  cases hc, cases h,
end
| (succ n) C (b :: L) 0 (succ l) h hc hl := b - 4 + int.nat_abs (4 - val_aux n C L 0 l begin
  exact succ_inj h
end hc begin
  exact pred_le_iff.mpr hl
end)
| (succ n) (a :: C) nil (succ c) (succ l) h hc hl := false.elim begin cases hl, end
| (succ n) nil (b :: L) (succ c) (succ l) h hc hl := false.elim begin cases hc, end
| (succ n) (a :: C) (b :: L) (succ c) (succ l) h hc hl := min
  (a - 2 + int.nat_abs (2 - val_aux n C (b :: L) c (succ l) (begin rw succ_add at h, exact succ_inj h end)
  (pred_le_iff.mpr hc) hl))
  (b - 4 + int.nat_abs (4 - val_aux n (a :: C) L (succ c) l (succ_inj h) hc (pred_le_iff.mpr hl)))


/--size of a yasle (number of components)-/
def yasize (y : yasle) : ℕ := multiset.card y.chains + multiset.card y.loops


import data.list.basic tactic.linarith
import tactic.omega tactic.apply

open list

-- changing one element of a list by at most d

structure list.modify (A : list ℤ) (B : list ℤ) (d : ℤ) :=
(n : ℕ)
(ha : n < A.length)
(hb : n < B.length)
(heq : A.remove_nth n = B.remove_nth n)
(bound : abs (A.nth_le n ha - B.nth_le n hb) ≤ d)

theorem list.modify_same {A : list ℤ} {B : list ℤ} {d : ℤ}
  (h : list.modify A B d) (m : ℕ) (hmA : m < A.length) (hmB : m < B.length)
  (hmn : h.n ≠ m) : A.nth_le m hmA = B.nth_le m hmB :=
begin
  sorry
end

def list.modify.symm (A B : list ℤ) (d : ℤ) 
(m : list.modify A B d) : list.modify B A d :=
{ n := m.n,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  bound := by rw [←neg_sub, abs_neg]; exact m.bound
}

structure game :=
(C : list ℤ) (L : list ℤ)

namespace game
--extensionaliti changes in new mathlib
@[ext] def ext (G1 G2 : game) : G1 = G2 ↔ G1.C = G2.C ∧ G1.L = G2.L :=
by cases G1; cases G2; simp

-- for use later, in the MITM proof
inductive modify (G1 G2 : game) (d : ℤ)
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

end game

open game

def list.min {X : Type*} [decidable_linear_order X] :
Π (L : list X), (L ≠ []) → X
| ([]) hL := false.elim $ hL rfl
| (x :: []) hL := x
| (x :: y :: L) _ := min x (list.min (y :: L) dec_trivial)

def list.min' (L : list ℤ) : ℤ :=
if h : L = [] then 0 else list.min L h

def game.rec_on_size' (C : game → Sort*) :
(∀ G : game, G.size = 0 → C G) → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ m : ℕ, ∀ G : game, G.size = m → C G := λ z ih n, nat.rec z ih n

universe u
--@[elab_as_eliminator]
def game.rec_on_size {C : game → Sort u} :
C game.zero → (∀ n : ℕ, 
  (∀ G : game, G.size = n → C G) → (∀ G : game, G.size = n + 1 → C G)) →
  ∀ G : game, C G :=
λ z ih G, @game.rec_on_size' C (λ H hH, (by rwa eq_zero_of_size_zero hH : C H)) ih (G.size) _ rfl

def list.aux_fun (m tf vL : ℤ) := m - tf + abs(tf - vL)

theorem list.aux_fun_L1 {m1 m2 tf vL d : ℤ} (hm : abs (m1 - m2) ≤ d) :
  abs(list.aux_fun m1 tf vL - list.aux_fun m2 tf vL) ≤ d :=
begin
  sorry 
end

theorem list.aux_fun_L2 {m m tf vL1 vL2 d : ℤ} (hm : abs (vL1 - vL2) ≤ d) :
  abs(list.aux_fun m tf vL1 - list.aux_fun m tf vL2) ≤ d :=
begin
  sorry 
end

lemma abs_min_sub_min {a b x y d : ℤ} (hab : abs (a - b) ≤ d)
  (hxy : abs (x - y) ≤ d) : abs (min a x - min b y) ≤ d :=
begin
  rw abs_le at *,
  cases hab; cases hxy,
  unfold min,
  split_ifs; split; linarith,
end

-- need this for list.min'
theorem list.min_change (L M : list ℤ) (hL : L ≠ []) (hLM : L.length = M.length) (hM : M ≠ []) (d : ℤ)
(hdist : ∀ (i : ℕ) (hiL : i < L.length) (hiM : i < M.length), abs (L.nth_le i hiL - M.nth_le i hiM) ≤ d) :
  abs (L.min hL - M.min hM) ≤ d :=
begin
  show abs (list.min L hL - list.min M hM) ≤ d,
  revert M,
  cases L with n L,
    contradiction,
  revert n,
  induction L with n1 L IH,
  {
    intros n _ M hM1 _ hi,
    change 1 = length M at hM1,
    symmetry' at hM1,
    rw length_eq_one at hM1,
    cases hM1 with m hM1,
    simp only [hM1],
    show abs (n - m) ≤ d,
    convert hi 0 (zero_lt_one) _,
    simp only [hM1],
    refl,
    rw hM1,
    exact zero_lt_one,
  },
  { intros n _ M hM _ hi,
    cases M with m M, cases hM,
    cases M with m1 M, cases hM,
    unfold list.min,
    have hmn : abs (n - m) ≤ d,
      exact hi 0 dec_trivial dec_trivial,
    replace hM := nat.succ_inj hM,
    have hyp : (∀ (i : ℕ) (hiL : i < length (n1 :: L)) (hiM : i < length (m1 :: M)),
      abs (nth_le (n1 :: L) i hiL - nth_le (m1 :: M) i hiM) ≤ d),
      intros i hiL hiM,
      exact hi (i + 1) (nat.succ_lt_succ hiL) (nat.succ_lt_succ hiM),
    have h := IH n1 dec_trivial (m1 :: M) hM dec_trivial hyp,
    exact abs_min_sub_min hmn h}
end

definition list.value_i (tf : ℤ) :
  ∀ (n : ℕ) (L : list ℤ) (i : fin n) (hL : L.length = n), ℤ
| (0) L i h := begin exfalso, sorry end -- i gives a contradiction
| (d + 1) L i h := list.aux_fun (L.nth_le i.val (by rw h; exact i.is_lt)) tf (list.min' (list.of_fn $
    λ (j : fin d), list.value_i d (L.remove_nth i.val) j begin
      rw list.length_remove_nth L i.val _,
        rw h, simp,
      rw h, exact i.is_lt,
    end))

-- this looks easier
theorem eq_size_of_modify_list (l1 l2 : list ℤ ) (d : ℤ) (h : list.modify l1 l2 d) : l1.length = l2.length :=
begin
  cases h, have P : length(remove_nth l1 h_n) = length(remove_nth l2 h_n), rw h_heq, 
  rw length_remove_nth  at P, rw length_remove_nth  at P,  have Q : ¬ h_n < 0, simp,
  cases l1, dsimp at h_ha, exfalso, finish, cases l2, dsimp at h_hb,
  exfalso, finish, finish, exact h_hb, exact h_ha,
  end

theorem MITM_baby (tf : ℤ) (L1 L2 : list ℤ) (d : ℤ) (h : list.modify L1 L2 d)
  (n : ℕ) (hL1 : L1.length = n) (hL2 : L2.length = n) (i : fin n) :
  abs (list.value_i tf n L1 i hL1 - list.value_i tf n L2 i hL2) ≤ d :=
begin
  revert L1 L2,
  induction n with d hd,
    cases i, cases i_is_lt,
  intros L1 L2 h hL1 hL2,
  unfold list.value_i,
  by_cases hin : h.n = i.val,
  { -- i = place where lists differ
    have heq := h.heq,
    rw hin at heq,
    simp only [heq],
    apply list.aux_fun_L1,
    convert h.bound,
      exact hin.symm,
      exact hin.symm,
    },
  { -- i ≠ place where lists differ
    rw list.modify_same h i.val _ (begin rw hL2, exact i.is_lt end) hin,
    apply list.aux_fun_L2,
      exact 37, -- note: this might be the right number in all cases
    -- apply "lists differ by at most d -> min differs by at most d"
    -- you will need a function
    -- Π (h : list.modify A B d), Π (m : ℕ), m ≠ h.n → m < A.length →
    --  list.modify (A - m) (B - m) d 
    -- where A - m is A.remove_nth m 
    sorry 
    }
end

  


#exit
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
    end.




-- this looks easier
theorem eq_size_of_modify {G1 G2 : game} {d : ℤ} (h : game.modify G1 G2 d) : G1.size = G2.size :=
begin
  cases h, 
  unfold size, rw h_a_1, rw @add_right_cancel_iff _ _ (G2.L).length,  
  exact eq_size_of_modify_list G1.C G2.C d h_a,
  unfold size, rw h_a_1, rw @add_left_cancel_iff _ _ (G2.C).length,  
  exact eq_size_of_modify_list G1.L G2.L d h_a,
end



#exit 

-- this is the big challenge
theorem MITM (G1 G2 : game) (d : ℤ) (h1 : game.modify G1 G2 d) (h2 : 0 ≤ d):
 abs(G1.value - G2.value) ≤ d :=
begin
  revert G1,
  revert G2,
  apply @game.rec_on_size (λ G2, ∀ G1, modify G1 G2 d → 
  abs (game.value G1 - game.value G2) ≤ d),
  -- this might be tricky!
  { intros G h1, have h3 : G.size = zero.size := eq_size_of_modify h1,
  rw size_zero at h3, have H := eq_zero_of_size_zero h3, 
  rw H, show  0 ≤ d, exact h2},
  { intros n H G1 p G2 p2,
    have hs := eq_size_of_modify p2,
    rw p at hs,
    unfold game.value,
    unfold game.rec_on_size,
    unfold game.rec_on_size',
--    dsimp,
    simp only [hs, p, (nat.succ_eq_add_one n).symm],
    apply list.min_change,
    { rw [length_append, length_of_fn, length_of_fn, length_append, length_of_fn, length_of_fn],
      show G2.size = G1.size,
      rw [p, hs]},
    intros i hiL hiM,
    rw [length_append, length_of_fn, length_of_fn] at hiL hiM,
    dsimp, 
    sorry
  },
end
/- todo

1) Fill in sorrys (first two shouldn't be hard, third might be more of a challenge, but I am pretty
sure I can do it)
2) Prove that if `h : game.modify G1 G2 d` then int.nat_abs(G1.value - G2.value) <= d by induction on size

-/


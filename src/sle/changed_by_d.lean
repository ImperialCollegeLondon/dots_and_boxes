import data.multiset
-- changing one element of a multiset by at most d

structure multiset.modify (A : multiset ℤ) (B : multiset ℤ) (d : ℤ) :=
(a : ℤ) (ha : a ∈ A)
(b : ℤ) (hb : b ∈ B)
(heq : A.erase a = B.erase b)
(hle : a - b ≤ d ∧ b - a ≤ d)

def multiset.modify.bij (A : multiset ℤ) (B : multiset ℤ) (d : ℤ) (m : multiset.modify A B d) :
  {a : ℤ | a ∈ A} → {b : ℤ | b ∈ B} := λ x, dite (x.val = m.a) (λ h, ⟨m.b, m.hb⟩)
  (λ h, ⟨x.val, begin
    sorry
  end⟩)

def multiset.modify.symm (A B : multiset ℤ) (d : ℤ) 
(m : multiset.modify A B d) : multiset.modify B A d :=
{ a := m.b,
  b := m.a,
  ha := m.hb,
  hb := m.ha,
  heq := m.heq.symm,
  hle := m.hle.symm
}

structure game :=
(C : multiset ℤ) (L : multiset ℤ)

inductive game.modify (G1 G2 : game) (d : ℤ)
| modifyc : multiset.modify G1.C G2.C d → (G1.L = G2.L) → game.modify
| modifyl : multiset.modify G1.L G2.L d → (G1.C = G2.C) → game.modify

inductive moves (G : game)
| chain : Π (c : ℤ), c ∈ G.C → moves
| loop : Π (l : ℤ), l ∈ G.L → moves

#print prefix moves

#check moves.rec

variables G1 G2 : game
#check @moves.rec G1 (λ _, moves G2)

def moves.bij (G1 G2 : game) (d : ℤ) (m : game.modify G1 G2 d) (h : moves G1) : moves G2 :=
m.rec
  (λ mc hl, sorry) 
  (sorry)

def game.size (G : game) : ℕ := multiset.card G.C + multiset.card G.L

#exit

def moves_dict (G1 G2 : game) (d : ℤ) (h : game.modify G1 G2 d) :
  equiv (moves G1) (moves G2) :=
{ to_fun := 

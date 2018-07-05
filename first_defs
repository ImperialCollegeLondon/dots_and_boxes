import data.multiset

@[derive decidable_eq]
structure simple_loony_endgame :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 4)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, x ≥ 8)
(long_loops_are_even : ∀ x ∈ long_loops, 2 ∣ x)

def distel (m : multiset nat): nat := multiset.card (multiset.erase_dup (m))

def size_G (G : simple_loony_endgame) :=
multiset.card (simple_loony_endgame.long_loops G) + multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G


def fcv_G (G : simple_loony_endgame) :=
simple_loony_endgame.three_chains G + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G + multiset.card (simple_loony_endgame.long_loops G) 
+ multiset.card (simple_loony_endgame.long_chains G) 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_chains G)) + 1)*4 
- (multiset.card (multiset.erase_dup (simple_loony_endgame.long_loops G)) + 2)*8 

def tb_G (G : simple_loony_endgame) :=
if size_G G = 0 then 0
else if multiset.card (simple_loony_endgame.long_chains G) + simple_loony_endgame.three_chains G = 0 then 8
else if multiset.card (simple_loony_endgame.long_loops G) + simple_loony_endgame.four_loops G 
+ simple_loony_endgame.six_loops G = 0 then 4
else if simple_loony_endgame.long_chains G = multiset.zero then 6
else 4

def cv_G (G : simple_loony_endgame) := fcv_G G + tb_G G

inductive v_G (G : simple_loony_endgame)  
: sorry

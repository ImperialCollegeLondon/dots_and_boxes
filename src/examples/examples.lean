import yasle.basic -- basic defs for simple loony endgames

def G1 : sle :=
{ chains := {3, 3},
  chains_are_long := dec_trivial,
  loops := {4},
  loops_are_long_and_even := dec_trivial }

--#reduce value G1 -- overflows Lean memory
#eval value G1

-- 8 3-loops and a 4-chain
def G2 : sle :=
{ chains := multiset.repeat 3 8,
  chains_are_long := dec_trivial,
  loops := {4},
  loops_are_long_and_even := dec_trivial }

--#eval value G2 -- takes about 7 seconds to produce value 2

-- auxiliary function which computes the same thing in under a second
#eval val_aux 9 [3,3,3,3,3,3,3,3] [4] 8 1 (by norm_num) (by norm_num) (by norm_num)

/-
 notation: 9 = "value of a subgame with 9 components"
  [3,3,3,..,3] = chains
  [4] = loops
  8 = "the subgame has 8 chains"
  1 = "the subgame has 1 loop"
  "by norm_num" x 3 means "check that some equality/inequality is satisfied"

  The three checks are: (a) 8 + 1 = 9 (b) 8 <= number of chains (c) 1 <= number of loops

-/
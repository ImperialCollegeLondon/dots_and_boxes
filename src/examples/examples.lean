import sle.basic -- basic defs for simple loony endgames

def G1 : sle :=
{ chains := {3, 3},
  chains_are_long := dec_trivial,
  loops := {4},
  loops_are_long_and_even := dec_trivial }

--#reduce value G1 -- overflows Lean memory
#eval value G1

def G2 : sle :=
{ chains := multiset.repeat 3 20,
  chains_are_long := dec_trivial,
  loops := {4},
  loops_are_long_and_even := dec_trivial }

#eval value G2
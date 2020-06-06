# dots_and_boxes
Ellen's Dots and Boxes project

The folder src in this github repository contains all the code written for my final year research project in Mathematics, "Optimal gameplay in Dots and Boxes in Lean". 

We defined Dots and Boxes endgames containing only loops and chains, the value of such an endgame, and what it means for games to differ in one component by at most some integer d. 

MITM.lean is the formal verification that two games differing in one component by at most d, have values differing by at most d.

list.lemmas.simple and list.lemmas.long_lemmas contain lemmas about lists in Lean that had not been in mathlib at the time I started this project. (Some of them might have been added since then).

I have been using the version of mathlib corresponding to commit 324ae4b on https://github.com/leanprover/mathlib. This project used Lean version 3.4.2.

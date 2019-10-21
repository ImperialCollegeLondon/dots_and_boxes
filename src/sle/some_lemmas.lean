import data.multiset

open nat 




/-- cons_to_the_n x y m adds x copies of y to the multiset m-/
def cons_to_the_n : ℕ → ℕ →  multiset nat →  multiset nat
| 0 a b  := b
| 1 a b := (multiset.cons a b) 
| (succ n) a b := multiset.cons a (cons_to_the_n n a b) 


lemma cons_to_the_next_n (x n d : nat) ( α : multiset nat) : x ∈  cons_to_the_n n d α →  x ∈  cons_to_the_n (succ n) d α :=
begin
intro a, have h : x ∈ multiset.cons d (cons_to_the_n n d α), simp, right, by exact a, induction n with t Ht, unfold cons_to_the_n ,
unfold cons_to_the_n at a, rw multiset.mem_cons, right, by exact a, unfold cons_to_the_n, by exact h , 
end

lemma cons_to_the_prev_n (x t z : nat) (α : multiset nat) : x ∈ cons_to_the_n (succ t) z α → x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z :=
begin
intro a, induction t with p Hp, left, simp, unfold cons_to_the_n, unfold cons_to_the_n at a, finish, 
left, unfold cons_to_the_n at a, by exact a
end




lemma lenpre (x y z m : nat)(α : multiset nat) : (z ≥ y) → (∀ x ∈ α, x ≥ y) → (x ∈ cons_to_the_n m z α →  x ≥ y) :=
begin
intros M Q H, induction m with t Pt, unfold cons_to_the_n at H, finish, 
have Hn :  x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z,
 by exact cons_to_the_prev_n x t z α H, 
rw[multiset.mem_cons] at Hn, cases Hn, cases Hn, finish,  exact Pt Hn, rw Hn, finish
end

lemma still_even (x z n : nat) (α : multiset nat) : (2 ∣ z) → (∀ x ∈ α, 2 ∣ x) → (x ∈ cons_to_the_n n z α →  2 ∣ x) :=
begin
intros H P Q, induction n with t Ht, unfold cons_to_the_n at Q, finish,  
have Hn :  x ∈ multiset.cons z (cons_to_the_n t z α) ∨ x = z,
 by exact cons_to_the_prev_n x t z α Q, 
rw[multiset.mem_cons] at Hn, cases Hn, cases Hn, rw Hn, exact H, exact Ht Hn, rw Hn, exact H,
end

lemma new (a b c : nat) : a ≥ b → b ≥ c → a ≥ c :=
begin intros x y, by exact ge_trans x y,
end  


def distel (m : multiset nat): nat := multiset.card (multiset.erase_dup (m))

lemma add_long_all_long (α  : multiset nat) (n m : nat) : (∀ x ∈ α , x ≥ m) → (n ≥ m) → (∀ x ∈ multiset.cons n α, x ≥ m):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end

lemma add_even_all_even (α  : multiset nat) (n : nat) : (∀ x ∈ α , 2 ∣ x) → (2 ∣ n) → (∀ x ∈ multiset.cons n α, 2 ∣ x):=
begin
intros a b c d, rw[multiset.mem_cons] at d, cases d, rw[d], exact b, finish,
end
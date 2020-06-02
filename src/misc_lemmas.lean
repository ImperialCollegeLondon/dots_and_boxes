import data.int.basic  tactic.linarith


/- abs -/

/-- any integer greater than or equal to some absolute value is non-negative-/
lemma abs_le_nonneg {a b : ℤ } : abs(a) ≤ b → 0 ≤ b:=
begin 
have h : 0 ≤ abs(a),
  {show abs(a) ≥ 0, -- ≥ is defined via ≤ 
  exact abs_nonneg a}, -- absolute values are non-negative
intro x,
exact le_trans h x, -- using transitivity of ≤ 
end


/--the absolute value of a difference of values is greater than or equal
   to the the absolute value of the difference of their absolute values-/
theorem abs_abs_sub_abs_le (a b : ℤ) : abs (abs a - abs b) ≤ abs (a - b) :=
-- proof in term mode
abs_le.2 ⟨by rw [neg_le,neg_sub, abs_sub]; apply sub_abs_le_abs_sub, sub_abs_le_abs_sub a b⟩


/-- For any a, b, x, y, d in ℤ,
    if abs (a - b) ≤ d and abs (x - y) ≤ d, then abs (min a x - min b y) ≤ d-/
lemma abs_min_sub_min {a b x y d : ℤ} (hab : abs (a - b) ≤ d)
  (hxy : abs (x - y) ≤ d) : abs (min a x - min b y) ≤ d :=
begin
  rw abs_le at *, -- abs (m - n) ≤ d ↔ d ≤ m - n ∧ m - n ≤ d, for any m,n in ℤ 
  cases hab,
  cases hxy,
  unfold min, -- min a x = if (a ≤ x), then a, else x
              -- min b y = if (b ≤ y), then b, else y
  split_ifs; split; linarith, -- all cases Lean can solve by itself using linarith
end



/- lt -/

/--if there exists an element strictly between a and the sucessor of c in ℕ, then a is smaller than c -/
lemma lt_trans_of_succ {a b c : ℕ}: a < b → b < nat.succ c → a < c :=
begin
intros h1 h2,
rw nat.lt_succ_iff at h2, -- b < nat.succ c ↔ b ≤ c
exact lt_of_lt_of_le h1 h2, /- lt_of_lt_of_le says : for all x, y, z of some adequate type,
                               x < y → y ≤ z → a < z-/
end
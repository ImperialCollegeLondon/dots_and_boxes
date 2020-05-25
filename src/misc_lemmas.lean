import data.int.basic  tactic.linarith


/- abs -/

lemma abs_le_nonneg {a b : ℤ } : abs(a) ≤ b → 0 ≤ b:=
begin 
have h : 0 ≤ abs(a),
 show abs(a) ≥ 0,
 exact abs_nonneg a,
 intro x,
 exact le_trans h x,
end


-- put somewhere more sensible?
theorem abs_abs_sub_abs_le (a b : ℤ) : abs (abs a - abs b) ≤ abs (a - b) :=
abs_le.2 ⟨by rw [neg_le,neg_sub, abs_sub]; apply sub_abs_le_abs_sub, sub_abs_le_abs_sub a b⟩


lemma abs_min_sub_min {a b x y d : ℤ} (hab : abs (a - b) ≤ d)
  (hxy : abs (x - y) ≤ d) : abs (min a x - min b y) ≤ d :=
begin
  rw abs_le at *,
  cases hab; cases hxy,
  unfold min,
  split_ifs; split; linarith,
end


/- lt -/

/--if ∃ an element strictly between a and the sucessor of c in ℕ, then a is smaller than c -/
lemma lt_trans_of_succ {a b c : ℕ}: a < b → b < nat.succ c → a < c :=
begin
-- tactic state : a b c : ℕ
--                ⊢ a < b → b < nat.succ c → a < c

intros h1 h2,

-- tactic state : a b c : ℕ
--                h1 : a < b,
--                h2 : b < nat.succ c
--                ⊢ a < c

rw nat.lt_succ_iff at h2,
-- says b < nat.succ c ↔ b ≤ c

-- tactic state : a b c : ℕ
--                h1 : a < b,
--                h2 : b < nat.succ c
--                ⊢ a < c

exact lt_of_lt_of_le h1 h2,

-- tactic state : goals accomplished
end
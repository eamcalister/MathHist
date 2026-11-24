import Mathlib

/-! Euclid, Elements X.1 (modern real-number reading).
  Start from a; at each step remove more than half of what remains,
  i.e. the remainder satisfies r (n+1) < r n / 2.
  Then some remainder is smaller than the given magnitude b > 0. -/

theorem euclid_X_1 (a b : ℝ) (hb : 0 < b) (r : ℕ → ℝ)
    (h0 : r 0 = a) (hstep : ∀ n, r (n + 1) < r n / 2) :
    ∃ n, r n < b := by
  -- Each remainder is at most a / 2^n.
  have bound : ∀ n, r n ≤ a / 2 ^ n := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have h := hstep k
      have e : a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by
        rw [pow_succ, div_div]
      rw [e]
      linarith
  -- Archimedean step: 2^n eventually exceeds a / b.
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (a / b) (by norm_num : (1 : ℝ) < 2)
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have key : a < 2 ^ n * b := by
    have h1 := mul_lt_mul_of_pos_right hn hb
    have e : a / b * b = a := by field_simp [hb.ne']
    rw [e] at h1
    exact h1
  have small : a / 2 ^ n < b := by
    by_contra hc
    push_neg at hc
    have h2 := mul_le_mul_of_nonneg_left hc hp.le
    have e2 : (2 : ℝ) ^ n * (a / 2 ^ n) = a := by field_simp
    rw [e2] at h2
    linarith
  exact ⟨n, lt_of_le_of_lt (bound n) small⟩

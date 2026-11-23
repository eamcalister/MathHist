import Mathlib
/-! ... -/
def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + (n + 1)

theorem sum_first_n_naturals (n : ℕ) :
    2 * S n = n * (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [S]
      calc
        2 * (S n + (n + 1))
            = 2 * S n + 2 * (n + 1) := by ring
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 1) * ((n + 1) + 1) := by ring

import Mathlib

/-!-/

def S : ℕ → ℕ
  | 0 => 0
  | Nat.succ n => S n + Nat.succ n

theorem babys_first_induction (n : ℕ) :
    2 * S n = n * (n + 1) := by
  induction n with
  | zero =>
      rfl
  | succ k ih =>
      rw[S]
      rw[Nat.mul_add]
      rw[ih]
      rw[Nat.succ_eq_add_one]
      rw [Nat.add_assoc]
      norm_num
      rw [Nat.mul_comm k (k + 1)]
      rw [Nat.mul_comm 2 (k + 1)]
      rw[<-Nat.mul_add]
      -- induction step

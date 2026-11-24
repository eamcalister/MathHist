import Mathlib

/-!
Euclid, Elements X.1

Two unequal magnitudes being set out, if from the greater there is subtracted
a magnitude greater than its half, and from the remainder a magnitude greater
than its half, and so on continually, there will be left some magnitude which
is less than the lesser magnitude set out.

Magnitudes are modeled by real numbers. r k is the remainder after k
subtractions, so r 0 = a, and "subtracting more than half" means
r (k+1) < r k / 2.

Euclid's proof:
By V Def. 4, the lesser magnitude b can be multiplied until it exceeds a;
  call the multiple DE = (m+1)·b, divided into m+1 parts equal to b.
From DE subtract one part (not more than its half); from AB subtract more
  than its half. The remainder of DE still exceeds the remainder of AB.
Repeat until the parts of DE are used up except one, i.e. b itself.
-/

-- The step Euclid repeats: if X > Y, and from X we take away no more than half,
-- while from Y we take away more than half, then what is left of X exceeds
-- what is left of Y.
theorem euclid_X1_step {X Y X' Y' : ℝ} (hXY : Y < X) (hX : X / 2 ≤ X')
    (hY : Y' < Y / 2) : Y' < X' := by
  linarith

theorem euclid_X_1 (a b : ℝ) (hb : 0 < b) (r : ℕ → ℝ)
    (h0 : r 0 = a) (hstep : ∀ n, r (n + 1) < r n / 2) :
    ∃ n, r n < b := by
  -- Elements V, Def. 4: some multiple of b exceeds a.
  obtain ⟨m, hm⟩ := Archimedean.arch a hb
  have hm' : a < ((m + 1 : ℕ) : ℝ) * b := by
    rw [nsmul_eq_mul] at hm
    push_cast
    linarith
  -- After k subtractions from AB, and k parts removed from DE,
  -- the remainder of DE (j+1 parts) still exceeds the remainder of AB.
  have claim : ∀ k j : ℕ, a < ((k + j + 1 : ℕ) : ℝ) * b →
      r k < ((j + 1 : ℕ) : ℝ) * b := by
    intro k
    induction k with
    | zero =>
      intro j hj
      rw [h0]
      have e : (0 + j + 1 : ℕ) = j + 1 := by omega
      rw [e] at hj
      exact hj
    | succ k ih =>
      intro j hj
      have hj' : a < ((k + (j + 1) + 1 : ℕ) : ℝ) * b := by
        have e : (k + 1 + j + 1 : ℕ) = k + (j + 1) + 1 := by omega
        rw [← e]
        exact hj
      -- remainder of DE (j+2 parts) exceeds r k
      have hk := ih (j + 1) hj'
      have hjb : (0 : ℝ) ≤ (j : ℝ) * b := mul_nonneg (Nat.cast_nonneg j) hb.le
      -- remove one part from DE (not more than half),
      -- more than half from the remainder of AB
      apply euclid_X1_step hk _ (hstep k)
      push_cast
      nlinarith
  -- When only one part of DE is left, that part is b itself.
  refine ⟨m, ?_⟩
  have h := claim m 0 hm'
  norm_num at h
  exact h

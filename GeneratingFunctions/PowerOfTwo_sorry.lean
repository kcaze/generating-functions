import Mathlib
import GeneratingFunctions.PowerSeriesExtra

section
open PowerSeries

variable (a: ℕ → ℝ)
variable (A : ℝ⟦X⟧)
variable (ha_base_case : a 0 = 0)
variable (ha_recursion : ∀ n, a (n+1) = 2*(a n) + 1)
variable (A_def : A = mk a)

theorem A_generating_function : A = X * (1-(1:ℝ)•X)⁻¹ * (1-(2:ℝ)•X)⁻¹ := by
  have constantCoeff_A_eq_zero : constantCoeff ℝ A = 0 := by sorry

  let AdivX := divX A constantCoeff_A_eq_zero

  /- LHS of Eq (1.1.1): $\sum_{n \ge 0} a_{n+1}x^n = A(x)/x$. -/
  have LHS_eq_1_1_1 : mk (fun n => a (n+1)) = AdivX := by sorry

  /- RHS of Eq (1.1.1): $\sum_{n \ge 0} (2a_n + 1)x^n = 2A(x) + \frac{1}{1-x}$. -/
  have RHS_eq_1_1_1 : mk (fun n => 2*(a n) + 1) = (2:ℝ)•A + (1-(1:ℝ)•X)⁻¹ := by sorry

  /- Equating the two sides of Eq (1.1.1) -/
  have LHS_eq_RHS : AdivX = (2:ℝ)•A + (1-(1:ℝ)•X)⁻¹ := by sorry

  /- Multiplying both sides by X. -/
  have : A = X*((2:ℝ)•A + (1-(1:ℝ)•X)⁻¹) := by sorry

  /- Subtract 2*X*A. -/
  have : (1-(2:ℝ)•X) * A = X*(1-(1:ℝ)•X)⁻¹ := by sorry

  /- Conclude -/
  sorry

/- We'll skip this. -/
theorem partial_fraction_expansion : (1-(1:ℝ)•(X:ℝ⟦X⟧))⁻¹ * (1-(2:ℝ)•X)⁻¹ = 2 • (1-(2:ℝ)•X)⁻¹ - (1-(1:ℝ)•X)⁻¹ := by
  sorry

theorem a_formula : a n = 2^n - 1 := by
  set P : ℝ⟦X⟧ := 2 • (1-(2:ℝ)•X)⁻¹ with hP
  set Q : ℝ⟦X⟧ := (1-(1:ℝ)•X)⁻¹ with hQ

  cases n with
  | zero => simp [ha_base_case]
  | succ n => {
    have hA_partial_fraction : A = (X * (P-Q)) := by sorry

    have hP_coeff : (coeff ℝ) n P = 2^(n+1) := by sorry

    have hQ_coeff : (coeff ℝ) n Q = 1 := by sorry

    sorry
  }

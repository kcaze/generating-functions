import Mathlib
import GeneratingFunctions.PowerSeriesExtra

section
open PowerSeries
variable (f: ℕ → ℝ)
variable (F: ℝ⟦X⟧)
variable (h_base_case: f 0 = 0 ∧ f 1 = 1)
variable (h_recursion: ∀ n, f (n+2) = f (n+1) + f n)
variable (F_def: F = mk f)

theorem F_gf : F = X * (1-X-X^2)⁻¹ := by
  have h_eq_zero : (constantCoeff ℝ) (F-X) = 0 := by
    simp [F_def, h_base_case]

  /- LHS: $\sum_{n \ge 1} f_{n+1}x^n = \frac{F(x)-x}{x}$. -/
  have LHS : X*(mk (fun n => f (n+2))) = divX (F-X) h_eq_zero := by
    ext n
    rw [coeff_divX (F-X) h_eq_zero n]
    cases n with
    | zero => simp [F_def, h_base_case]
    | succ n => simp [coeff_succ_X_mul, F_def, coeff_X]

  /- RHS: $\sum_{n \ge 1} (f_n + f_{n-1})x^n = F(x) + xF(x)$. -/
  have RHS : X*(mk (fun n => f (n+1) + f n)) = F + X*F := by
    ext n
    cases n with
    | zero => simp [F_def, h_base_case]
    | succ n => simp [coeff_succ_X_mul, F_def]

  /- LHS = RHS from the defining recursion. -/
  have LHS_eq_RHS : divX (F-X) h_eq_zero = F + X*F := by
    rw [← LHS, ← RHS]
    ext n
    cases n with
    | zero => simp
    | succ n => simp [h_recursion]

  /- Multiply both sides by X -/
  have : F-X = X*F + X^2*F := by
    calc F-X = X*(divX (F-X) h_eq_zero) := by rw [← eq_mulX_divX (F-X) h_eq_zero]
           _ = X*F + X^2*F := by rw [LHS_eq_RHS]; ring

  /- Collect F terms. -/
  have : F*(1-X-X^2) = X := by
    calc F*(1-X-X^2) = F-(X*F+X^2*F) := by ring
                   _ = X := by rw [← this]; ring

  /- Conclude. -/
  nth_rewrite 1 [← this]
  have h_ne_zero : (constantCoeff ℝ) (1-X-X^2) ≠ 0 := by simp
  rw [mul_assoc, PowerSeries.mul_inv_cancel (1-X-X^2) h_ne_zero]
  ring
end

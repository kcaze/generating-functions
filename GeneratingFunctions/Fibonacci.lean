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

noncomputable def rplus := (1+√5)/2
noncomputable def rminus := (1-√5)/2
noncomputable def P : ℝ⟦X⟧ := 1-rplus•X
noncomputable def Q : ℝ⟦X⟧ := 1-rminus•X

theorem factor : (1:ℝ⟦X⟧)-X-X^2 = (1-rplus•X)*(1-rminus•X) := by
    rw [mul_sub_right_distrib, mul_sub_left_distrib, mul_sub_left_distrib]
    simp
    rw [← sub_add, smul_eq_C_mul, smul_eq_C_mul]
    nth_rewrite 2 [sub_sub]
    rw [← add_mul, smul_smul, C_add_C]
    rw [rplus, rminus]
    ring_nf
    simp
    ring_nf
    simp
    ring

theorem hP_ne_zero : constantCoeff ℝ P ≠ 0 := by simp [P]
theorem hQ_ne_zero : constantCoeff ℝ Q ≠ 0 := by simp [Q]

theorem inv_sub_inv'' : P⁻¹ - Q⁻¹ = (Q-P) * (P*Q)⁻¹ := by
    rw [inv_of_mul, sub_mul]
    rw [mul_comm, mul_assoc, PowerSeries.inv_mul_cancel Q hQ_ne_zero, ← mul_assoc, PowerSeries.mul_inv_cancel P hP_ne_zero]
    ring

theorem partial_fraction : (X:ℝ⟦X⟧)*(1-X-X^2)⁻¹ = (1/√5) • (P⁻¹ - Q⁻¹) := by
  rw [factor, inv_sub_inv'', P, Q]
  simp
  nth_rewrite 4 [smul_eq_C_mul]
  nth_rewrite 4 [smul_eq_C_mul]
  rw [← sub_mul, C_sub_C, mul_assoc]
  rw [← smul_eq_C_mul, smul_smul]
  nth_rewrite 2 [rplus, rminus]
  ring_nf
  simp [mul_inv_cancel]

theorem fibonacci_formula : f n = (1/√5) * (rplus^n - rminus^n) := by
  have : f n = (coeff ℝ) n F := by simp [F_def]
  rw [this, F_gf f F h_base_case h_recursion F_def, partial_fraction, P, Q]
  rw [← geometricSeries_eq_closed_form rplus, ← geometricSeries_eq_closed_form rminus]
  simp [geometricSeries]

end

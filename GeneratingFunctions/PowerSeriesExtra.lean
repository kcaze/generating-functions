import Mathlib

section
open PowerSeries

variable {k : Type*} [Field k]

noncomputable def divX (P: k⟦X⟧) (h: constantCoeff k P = 0) : k⟦X⟧ :=
  (exists_eq_mul_right_of_dvd (X_dvd_iff.mpr h)).choose

/- `geometricSeries r` = $\sum_{n \ge 0} r^nx^n$ -/
def geometricSeries {k: Type u} [Field k] (r : k) : PowerSeries k :=
  mk fun n => r^n

@[simp]
theorem PowerSeries.constantCoeff_mk (f : ℕ → k) : (constantCoeff k) (mk f) = f 0 := by
  rw [← coeff_zero_eq_constantCoeff]
  exact (coeff_mk 0 f)

lemma smul_mul_eq_mul_smul (P: k⟦X⟧) (Q: k⟦X⟧) (c: k)
    : c • P * Q = P * c • Q := by
  simp

lemma eq_mulX_divX (P: k⟦X⟧) (h: constantCoeff k P = 0) : P = X*(divX P h) := by
  unfold divX
  exact Exists.choose_spec (exists_eq_mul_right_of_dvd (X_dvd_iff.mpr h))

lemma coeff_divX (P: k⟦X⟧) (h: constantCoeff k P = 0) (n: ℕ)
    : (coeff k n (divX P h)) = coeff k (n+1) P := by
  simp [eq_mulX_divX P h]

/- $\sum_{n \ge 0} (a \cdot r^n)x^n = \frac{a}{1-rx}$ -/
lemma geometricSeries_eq_closed_form {k: Type u} [Field k] (r: k)
  : geometricSeries r = (1 - r•X)⁻¹ := by
  suffices h : (geometricSeries r) * (1-r•X) = 1 by
    have h' : constantCoeff k (1-r•X) ≠ 0 := by simp
    exact (eq_inv_iff_mul_eq_one h').mpr h
  ext n
  cases n with
  | zero => simp [geometricSeries]
  | succ n => {
    rw [mul_sub_left_distrib]
    suffices h : r ^ (n + 1) - r * r ^ n = 0 by simp [geometricSeries, h]
    ring
  }

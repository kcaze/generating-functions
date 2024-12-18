import Mathlib.RingTheory.PowerSeries.Inverse

section
open PowerSeries

variable {k : Type*} [Field k]
/-! Define $\large\frac{P(x)}{x}$ as the $\large Q(x)$ that satisfies $\large Q(x) \cdot x = P(x)$.-/
noncomputable def divX (P: k⟦X⟧) (h: constantCoeff k P = 0) : k⟦X⟧ :=
  (exists_eq_mul_right_of_dvd (X_dvd_iff.mpr h)).choose

/-! Define geometricSeries r as $\large\displaystyle\sum_{n \ge 0} r^nx^n$. -/
def geometricSeries {k: Type u} [Field k] (r : k) : PowerSeries k :=
  mk fun n => r^n

lemma smul_mul_eq_mul_smul (P: k⟦X⟧) (Q: k⟦X⟧) (c: k)
    : c • P * Q = P * c • Q := by
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

lemma C_add_C (a: k) (b: k): (C k) a + (C k) b = (C k) (a+b) := by
  exact Eq.symm (RingHom.map_add (C k) a b)

lemma C_sub_C (a: k) (b: k): (C k) a - (C k) b = (C k) (a-b) := by
  exact Eq.symm (RingHom.map_sub (C k) a b)

lemma inv_of_mul (P: k⟦X⟧) (Q: k⟦X⟧) : (P*Q)⁻¹ = P⁻¹*Q⁻¹ := by
  rw [MvPowerSeries.mul_inv_rev]
  ring_nf

lemma eq_mulX_divX (P: k⟦X⟧) (h: constantCoeff k P = 0) : P = X*(divX P h) := by
  unfold divX
  exact Exists.choose_spec (exists_eq_mul_right_of_dvd (X_dvd_iff.mpr h))

lemma coeff_divX (P: k⟦X⟧) (h: constantCoeff k P = 0) (n: ℕ)
    : (coeff k n (divX P h)) = coeff k (n+1) P := by
  simp only [eq_mulX_divX P h, coeff_succ_X_mul]

/-! Show that $\displaystyle\large\sum_{n \ge 0}  r^nx^n = \frac{1}{1-rx}$. -/
lemma geometricSeries_eq_closed_form {k: Type u} [Field k] (r: k)
  : geometricSeries r = (1 - r•X)⁻¹ := by
  /-sorry-/

  /-# This is an latex comment $\sum_{i=0}$. -/
  suffices h : (geometricSeries r) * (1-r•X) = 1 by
    have h' : constantCoeff k (1-r•X) ≠ 0 := by simp
    exact (eq_inv_iff_mul_eq_one h').mpr h
  ext n
  cases n with
  | zero => simp only [geometricSeries, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_mk,
    pow_zero, map_sub, constantCoeff_one, constantCoeff_smul, constantCoeff_X, smul_eq_mul,
    mul_zero, sub_zero, mul_one, coeff_one, ↓reduceIte]
  | succ n => {
    rw [mul_sub_left_distrib]
    suffices h : r ^ (n + 1) - r * r ^ n = 0 by simp [geometricSeries, h]
    ring_nf
  }

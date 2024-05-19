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

variable (a: ℕ → ℝ)
variable (A : ℝ⟦X⟧)
variable (ha_base_case : a 0 = 0)
variable (ha_recursion : ∀ n, a (n+1) = 2*(a n) + 1)
variable (A_def : A = mk a)

theorem A_generating_function : A = X * (1-(1:ℝ)•X)⁻¹ - (1-(2:ℝ)•X)⁻¹ := by
  have constantCoeff_A_eq_zero : constantCoeff ℝ A = 0 := by
    simp [A_def, ha_base_case]

  let AdivX := divX A constantCoeff_A_eq_zero

  /- LHS of Eq (1.1.1): $\sum_{n \ge 0} a_{n+1}x^n = A(x)/x$. -/
  have LHS_eq_1_1_1 : mk (fun n => a (n+1)) = AdivX := by
    ext n
    rw [coeff_divX]
    simp [A_def]

  /- RHS of Eq (1.1.1): $\sum_{n \ge 0} (2a_n + 1)x^n = 2A(x) + \frac{1}{1-x}$. -/
  have RHS_eq_1_1_1 : mk (fun n => 2*(a n) + 1) = (2:ℝ)•A + (1-(1:ℝ)•X)⁻¹ := by
    rw [← geometricSeries_eq_closed_form 1]
    ext n
    simp [A_def, geometricSeries]

  /- Equating the two sides of Eq (1.1.1) -/
  have LHS_eq_RHS : AdivX = (2:ℝ)•A + (1-(1:ℝ)•X)⁻¹ := by
    rw [← LHS_eq_1_1_1, ← RHS_eq_1_1_1]
    simp [ha_recursion]

-- lemma coeffGeometricSeries {k : Type u_1} [Field k] (c: k) (n: ℕ): (coeff k n) (1-c•X)⁻¹ = c^n := by
--   rw [coeff_inv n (1-c•X)]
--   cases n
--   simp

-- lemma geometric_series (r: ℝ) : (1-r•X)⁻¹ = (rescale r (invUnitsSub 1)) := by
--   have h_constantCoeff_neq_zero : constantCoeff ℝ (1-r•X) ≠ 0 := by
--     rw [← coeff_zero_eq_constantCoeff, map_sub]
--     simp

--   suffices h' : (rescale r (invUnitsSub 1)) * (1-r•X)  = 1
--     from (PowerSeries.inv_eq_iff_mul_eq_one h_constantCoeff_neq_zero).mpr h'

--   rw [mul_sub_left_distrib]
--   ext n
--   cases n
--   -- n = 0
--   simp
--   -- n ≥ 1
--   simp
--   rw [pow_succ]
--   ring


-- -- -- A(x) = x / ((1-x) * (1-2x))
-- lemma A_formula (a: ℕ → ℝ) (ha_base_case : a 0 = 0) (ha_recursion : ∀ n, a (n+1) = 2*(a n) + 1)
--     : mk a = X * (1-1•X)⁻¹ * (1-2•X)⁻¹ := by
--   let A := mk a
--   have h : PowerSeries.constantCoeff ℝ A = 0 := by
--     exact ha_base_case

--   -- A(x)/x = 2*A(x) + 1/(1-x)
--   have eq₁ : divX A h = 2•A + (1-X)⁻¹ := by
--     ext n
--     have h₁ : (coeff ℝ n) (divX A h) = a (n+1) := by
--       rw [← coeff_succ_mul_X, mul_comm, ← eq_mulX_divX]
--       exact (coeff_mk (n+1) a)
--     have h₂ : (coeff ℝ n) (2•A + (1-1•X)⁻¹) = 2*(a n) + 1 := by
--       rw [map_add, coeff_smul n A 2, ← geometricSeries_eq_closed_form 1]
--       simp [coeff_mk n a]
--     rw [h₁, h₂]
--     simp [ha_recursion]

--   /- A(x) = 2*x*A(x) + x/(1-x) -/
--   have eq₂ : A = 2•(X*A) + X*(invUnitsSub 1) := by
--     calc
--       /- A(x) = x * (A(x)/x) -/
--       A = X * (divX A h) := by simp [eq_mulX_divX A h]
--       /- x * (A(x)/x) = x * (2*A(x) + 1/(1-x)) -/
--       _ = X * (2•A + invUnitsSub 1) := by rw [eq₁]
--       /- x*(2*A(x) + 1/(1-x)) = 2*x*A(x) + x/(1-x) -/
--       _ = 2•(X*A) + X*(invUnitsSub 1) := by ring_nf

--   -- (1-2x)*A = x/(1-x)
--   have eq₃ : (1 - 2•X)*A = X*(invUnitsSub 1) := by
--     ring_nf
--     nth_rewrite 2 [eq₂]
--     ring_nf

--   -- have eq₄ : (1-(2:ℝ)•X)⁻¹ = (rescale 2 (invUnitsSub 1)) := by
--   --   apply (geometric_series 2)

--   -- have eq₅ : (1-(2:ℝ)•X)⁻¹ * (1-(2:ℝ)•X) = 1 := by
--   --   have h : constantCoeff ℝ (1-(2:ℝ)•X) ≠ 0 := by
--   --     rw [map_sub, ← coeff_zero_eq_constantCoeff, coeff_smul, coeff_zero_X]
--   --     simp
--   --   exact (PowerSeries.inv_mul_cancel (1-(2:ℝ)•X) h)

--   have eq₆ : A = X * (invUnitsSub 1) * (rescale 2 (invUnitsSub 1)) := by
--     calc
--       A = 1 * A := by simp
--       _ = (1-(2:ℝ)•X)⁻¹ * (1-(2:ℝ)•X) * A := by rw [eq₅]
--       _ = (rescale 2 (invUnitsSub 1)) * (1-(2:ℝ)•X) * A := by rw [eq₄]
--       _ = (rescale 2 (invUnitsSub 1)) * X * (invUnitsSub 1) := by rw [mul_assoc, eq₃, ← mul_assoc]
--       _ = X * (invUnitsSub 1) * (rescale 2 (invUnitsSub 1)) := by ring

--   -- rw [← eq₆]

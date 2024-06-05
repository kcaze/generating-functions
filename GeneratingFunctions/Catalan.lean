import LatexInLean
import Mathlib

show_panel_widgets [latex]

/-! Goal: Show that $\large\displaystyle\sum_{n \ge 0} c_nx^n = \frac{1-\sqrt{1-4x}}{2x}$,
    where $c_n$ is the $n$-th Catalan number.-/

/-! Inductively define $\displaystyle\binom{r}{k}$ where $r \in \mathbb{R}$ and $k \in \mathbb{N}$. -/
noncomputable def Real.choose : ℝ → ℕ → ℝ
  | _, 0 => 1
  | r, k + 1 => r/(k+1)*(Real.choose (r-1) k)

/-! Define the multichoose function. -/
noncomputable def Real.multichoose (r : ℝ) (k : ℕ) : ℝ :=
  Real.choose (r+k-1) k

/-! Prove that $\mathbb{R}$ is a binomial ring. -/
noncomputable instance Real.instBinomialRing : BinomialRing ℝ where
  nsmul_right_injective n hn r s hrs := by {
    simp [hn] at hrs
    exact hrs
  }
  multichoose := Real.multichoose
  factorial_nsmul_multichoose r n := by
    induction' n with n ih
    case zero => {
      simp [Real.multichoose, Real.choose]
    }
    case succ => {
      rw [Polynomial.ascPochhammer_smeval_eq_eval] at ih
      rw [Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_succ_eval, ← ih]
      unfold multichoose
      nth_rewrite 1 [choose]
      rw [Nat.cast_add, Nat.cast_one]
      conv in (r + (↑n + 1) - 1) => ring_nf
      conv in (r + (↑n + 1) - 1 - 1) => ring_nf
      nth_rewrite 1 [Nat.factorial]
      field_simp
      ring_nf
    }


-- open PowerSeries
-- /-! Catalan generating function $\displaystyle\large C(x) \coloneqq \sum_{n \ge 0} c_n$. -/
-- def C : ℝ⟦X⟧ := PowerSeries.mk (fun n => ↑(catalan n))

-- /-! Generating function for $\displaystyle\large (1+rx)^\alpha \coloneqq \sum_{n \ge 0} \binom{\alpha}{n}r^nx^n$.-/
-- def BinomialSeries (r:ℝ) (α:ℝ) := mk (fun n => Ring.choose α n)

-- /-! Proof that for $\large n \in \mathbb{N}$, we have $\displaystyle \large \left(\sum_{n \ge 0} \binom{1/n}{n}r^nx^n\right)^n = 1+rx$.-/

-- theorem C =

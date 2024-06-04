import LatexInLean
import Mathlib

show_panel_widgets [latex]

noncomputable def Real.choose : ℝ → ℕ → ℝ
  | _, 0 => 1
  | n, k + 1 => n/(k+1)*(Real.choose (n-1) k)

noncomputable def Real.multichoose (n : ℝ) (k : ℕ) : ℝ :=
  Real.choose (n+k-1) k


instance Real.instBinomialRing : BinomialRing ℝ where
  nsmul_right_injective n hn r s hrs := by {
    simp [hn] at hrs
    exact hrs
  }
  multichoose := Real.multichoose
  factorial_nsmul_multichoose r n := by
    rw [← Polynomial.eval₂_eq_smeval ℕ Real.instNatCast.natCast r (ascPochhammer ℕ n)]


-- open PowerSeries
-- /-! Catalan generating function $\displaystyle\large C(x) \coloneqq \sum_{n \ge 0} c_n$. -/
-- def C : ℝ⟦X⟧ := PowerSeries.mk (fun n => ↑(catalan n))

-- /-! Generating function for $\displaystyle\large (1+rx)^\alpha \coloneqq \sum_{n \ge 0} \binom{\alpha}{n}r^nx^n$.-/
-- def BinomialSeries (r:ℝ) (α:ℝ) := mk (fun n => Ring.choose α n)

-- /-! Proof that for $\large n \in \mathbb{N}$, we have $\displaystyle \large \left(\sum_{n \ge 0} \binom{1/n}{n}r^nx^n\right)^n = 1+rx$.-/

-- theorem C =

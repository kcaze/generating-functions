import Mathlib
import GeneratingFunctions.PowerSeriesExtra

section
open PowerSeries

noncomputable def Y : ℝ⟦X⟧ := PowerSeries.X

theorem partial_fraction_expansion (A B C:ℝ⟦X⟧):
    (1-(2:ℝ)•Y+(2:ℝ)•Y*Y) * (1-Y)⁻¹ * (1-Y)⁻¹ * (1-(2:ℝ)•Y)⁻¹ * (1-(2:ℝ)•Y)⁻¹
    = A * (1-Y)⁻¹ * (1-Y)⁻¹ + B * (1-Y)⁻¹ + C * (1-(2:ℝ)•Y)⁻¹ := by
  sorry

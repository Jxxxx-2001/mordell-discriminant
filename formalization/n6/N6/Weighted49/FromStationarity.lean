import N6.Weighted49.Cover
import N6.ResultantMinors.Necessity
import review.Dcolon1Chart

set_option autoImplicit false

namespace N6.Weighted49
open N6.SparseCheck N6.ResultantMinors

/-- A one-direction coverage statement with every chart denominator discharged. -/
theorem cover_from_original (b c d e : ℂ) (hb : b ≠ 0)
    (hD : N6.Chart.originalD b c d e ≠ 0)
    (h0 : N6.Chart.E0 b c d e = 0) (h1 : N6.Chart.E1 b c d e = 0)
    (h2 : N6.Chart.E2 b c d e = 0) (h3 : N6.Chart.E3 b c d e = 0) :
    globalP35 (b^2) = 0 ∧ coordinate_c (b^2) c = 0 ∧
      coordinate_k (b^2) (d/b) = 0 ∧ coordinate_e (b^2) e = 0 := by
  have ratio := N6.Chart.ratio_substitution b d hb
  have hd : N6.Chart.D (b^2) c (d/b) e ≠ 0 := by
    rw [← N6.Chart.discriminant_substitution, ratio]
    exact hD
  have hB : b^2 ≠ 0 := pow_ne_zero 2 hb
  let t : ℂ := ((b^2) * N6.Chart.D (b^2) c (d/b) e)⁻¹
  let x : Fin 5 → ℂ := point (b^2) c (d/b) e t
  have f0 := N6.Chart.quotient_zero0 b c (d/b) e hb (by simpa only [ratio] using h0)
  have f1 := N6.Chart.quotient_zero1 b c (d/b) e hb (by simpa only [ratio] using h1)
  have f2 := N6.Chart.quotient_zero2 b c (d/b) e hb (by simpa only [ratio] using h2)
  have f3 := N6.Chart.quotient_zero3 b c (d/b) e hb (by simpa only [ratio] using h3)
  have sat := N6.Chart.saturation (b^2) c (d/b) e hB hd
  have result := cover_from_inputs x
    (by simpa only [N6.Dcolon1.chartF0, x, point_eval4, point_eval3, point_eval2, point_eval1] using f0)
    (by simpa only [N6.Dcolon1.chartF1, x, point_eval4, point_eval3, point_eval2, point_eval1] using f1)
    (by simpa only [N6.Dcolon1.chartF2, x, point_eval4, point_eval3, point_eval2, point_eval1] using f2)
    (by simpa only [N6.Dcolon1.chartF3, x, point_eval4, point_eval3, point_eval2, point_eval1] using f3)
    (by simpa only [N6.Dcolon1.chartD, x, t, point_eval0, point_eval4,
      point_eval3, point_eval2, point_eval1] using sat)
  simpa only [x, point_eval4, point_eval3, point_eval2, point_eval1] using result

theorem cover_from_scaled_maximum {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (b c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 b c d e) (hb : b ≠ 0) :
    globalP35 (b^2) = 0 ∧ coordinate_c (b^2) c = 0 ∧
      coordinate_k (b^2) (d/b) = 0 ∧ coordinate_e (b^2) e = 0 := by
  obtain ⟨h0,h1,h2,h3⟩ := scaled_maximum_original_equations hz hα b c d e hp
  exact cover_from_original b c d e hb (scaled_maximum_originalD_ne hz hα b c d e hp)
    h0 h1 h2 h3

#print axioms cover_from_original
#print axioms cover_from_scaled_maximum
end N6.Weighted49

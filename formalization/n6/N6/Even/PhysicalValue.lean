import N6.Even.ValuePhysical
import N6.Even.ProgramActualBindings
import N6.ResultantMinors.Necessity

set_option autoImplicit false
namespace N6.Even
open N6.SparseCheck Polynomial
open ProgramData

theorem scaled_maximum_physical_coefficients {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (c e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 0 c 0 e) :
    actualR4 c e=actualD c e*(N6.physicalScalar (N6.scaleConfiguration α z) : ℂ) ∧
    actualR02 c e=actualD c e*star c*
      (N6.physicalScalar (N6.scaleConfiguration α z) : ℂ)^2 := by
  let w := N6.scaleConfiguration α z
  let y := N6.dualConfiguration w
  have hA : N6.rootCoefficientA w=1 := by
    change (N6.rootPolynomial w).coeff 4=1
    rw [hp]
    norm_num [N6.coefficientSextic]
  have hD : actualD c e=N6.complexDiscriminant w :=
    (actualD_chart c e).trans
      (N6.ResultantMinors.originalD_eq_discriminant (N6.scaled_dualStationaryPair hz hα)
        0 c 0 e hp)
  constructor
  · rw [actualR4_coefficient]
    have h := N6.ResultantMinors.scaled_maximum_original_r4 hz hα hA 0 c 0 e hp
    simpa only [←actualD_chart] using h
  · have hr : (N6.stationaryR0 w y).coeff 2 =
        value (N6.ResultantMinors.point 0 c 0 e 0)
          (N6.ResultantMinors.extractY 2 N6.ResultantMinors.D063) := by
      rw [N6.ResultantMinors.stationaryR0_eq_liftY
        (N6.scaled_dualStationaryPair hz hα) 0 c 0 e hp,
        N6.ResultantMinors.coeff_liftY]
    have hphys : (N6.stationaryR0 w y).coeff 2 = N6.complexDiscriminant w *
        ((starRingEnd ℂ) c*(N6.forceParameter w : ℂ)^4) := by
      rw [N6.physical_resultant_coefficient w y (N6.forceParameter w)
        (N6.scaled_dual_physical hz hα) 2,hp]
      norm_num [N6.coefficientSextic]
    have haPow : (N6.physicalScalar w : ℂ)^2=(N6.forceParameter w : ℂ)^4 := by
      simp only [N6.physicalScalar,Complex.ofReal_pow]
      ring
    calc
      actualR02 c e = (N6.stationaryR0 w y).coeff 2 :=
        (actualR02_coefficient c e).trans hr.symm
      _ = N6.complexDiscriminant w*((starRingEnd ℂ) c*(N6.forceParameter w : ℂ)^4) := hphys
      _ = actualD c e*star c*(N6.physicalScalar w : ℂ)^2 := by
        rw [←hD,haPow]
        change actualD c e*(star c*(N6.forceParameter w : ℂ)^4) = _
        ring

theorem even_scaled_maximum_value_bound {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (c e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 0 c 0 e) :
    (N6.physicalScalar (N6.scaleConfiguration α z))^15*
      Complex.normSq (actualD c e)/(5^30 : ℝ) < (6 : ℝ)^12 := by
  have heq := N6.ResultantMinors.scaled_maximum_original_equations hz hα 0 c 0 e hp
  have hd := N6.ResultantMinors.scaled_maximum_originalD_ne hz hα 0 c 0 e hp
  have ha : 0<N6.physicalScalar (N6.scaleConfiguration α z) :=
    sq_pos_of_pos (N6.scaled_forceParameter_pos hz hα)
  obtain ⟨h4,h2⟩ := scaled_maximum_physical_coefficients hz hα c e hp
  exact physical_value_bound_from_raw c e (N6.physicalScalar (N6.scaleConfiguration α z))
    heq.2.1 heq.2.2.2 hd ha h4 h2

#print axioms scaled_maximum_physical_coefficients
#print axioms even_scaled_maximum_value_bound
end N6.Even

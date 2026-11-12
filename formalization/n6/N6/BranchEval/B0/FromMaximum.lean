import N6.BranchEval.B0.PhysicalValue
import N6.BranchEval.B0.FactorBindingGround
import N6.Weighted49.FromStationarity
import N6.Analysis.SecondMoment
import N6.Analysis.GenericValue

set_option autoImplicit false

namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.ResultantMinors

theorem factor_onlyB : N6.BranchEval.onlyB N6.Weighted49.FactorCover.factor0Data = true := by
  decide +kernel

theorem scaled_maximum_impossible {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0)
    (hA : N6.rootCoefficientA (N6.scaleConfiguration α z) = 1)
    (b c d e : ℂ) (hb : b ≠ 0)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) = N6.coefficientSextic 1 b c d e)
    (hf : value (point (b^2) 0 0 0 0) N6.Weighted49.FactorCover.factor0Data = 0) : False := by
  let k := d/b
  let x : Fin 5 → ℂ := point (b^2) c k e 0
  have ratio : b*k=d := N6.Chart.ratio_substitution b d hb
  have hcoords := N6.Weighted49.cover_from_scaled_maximum hz hα b c d e hp hb
  have hfc : value x program.factor = 0 := by
    rw [factor_matches_actual, N6.BranchEval.value_eq_bEval x _ factor_onlyB]
    rw [N6.BranchEval.value_eq_bEval _ _ factor_onlyB] at hf
    exact hf
  have hc : N6.Weighted49.coordinate_c (x 4) (x 3) = 0 := hcoords.2.1
  have hk : N6.Weighted49.coordinate_k (x 4) (x 2) = 0 := hcoords.2.2.1
  have he : N6.Weighted49.coordinate_e (x 4) (x 1) = 0 := hcoords.2.2.2
  have hDchart : originalD (x 4) (x 3) (x 2) (x 1) = N6.Chart.originalD b c d e := by
    change originalD (b^2) c k e = _
    rw [originalD_chart, ratio]
  have hDne : originalD (x 4) (x 3) (x 2) (x 1) ≠ 0 := by
    rw [hDchart]
    exact scaled_maximum_originalD_ne hz hα b c d e hp
  have hRphys : originalR4 (x 4) (x 3) (x 2) (x 1) =
      originalD (x 4) (x 3) (x 2) (x 1) *
        (N6.physicalScalar (N6.scaleConfiguration α z) : ℂ) := by
    change originalR4 (b^2) c k e = _
    rw [originalR4_actual, ratio, hDchart]
    exact scaled_maximum_original_r4 hz hα hA b c d e hp
  have ha := N6.scaled_maximum_normalized_physicalScalar_bounds hz α hA
  obtain ⟨D,V,hD,hV,hbound⟩ := physical_value x _ ⟨ha.1.le,ha.2⟩ hfc hc hk he hDne hRphys
  have hDactual : N6.complexDiscriminant (N6.scaleConfiguration α z) = (D : ℂ) := by
    rw [← originalD_eq_discriminant (N6.scaled_dualStationaryPair hz hα) b c d e hp]
    exact hDchart.symm.trans hD
  exact (N6.GenericValue.exclude_real_branch z hz.1 α hα _ D V rfl hDactual hV hbound) hz

#print axioms scaled_maximum_impossible
end N6.BranchEval.B0.ProgramData

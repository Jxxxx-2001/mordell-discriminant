import N6.BranchEval.B0.FromMaximum
import N6.BranchEval.B1.FromMaximum
import N6.BranchEval.B2.FromMaximum
import N6.BranchEval.B3.FromMaximum
import N6.BranchEval.B4.FromMaximum
import N6.BranchEval.B5.FromMaximum
import N6.Weighted49.FactorCover
import N6.Weighted49.FromStationarity

set_option autoImplicit false

namespace N6.BranchEval
open N6.SparseCheck N6.ResultantMinors

theorem generic_scaled_maximum_impossible {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0)
    (hA : N6.rootCoefficientA (N6.scaleConfiguration α z) = 1)
    (b c d e : ℂ) (hb : b ≠ 0)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) = N6.coefficientSextic 1 b c d e) : False := by
  have hcover := N6.Weighted49.cover_from_scaled_maximum hz hα b c d e hp hb
  have factors := N6.Weighted49.FactorCover.cover (b^2) hcover.1
  rcases factors with h0 | h1 | h2 | h3 | h4 | h5
  · exact N6.BranchEval.B0.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h0
  · exact N6.BranchEval.B1.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h1
  · exact N6.BranchEval.B2.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h2
  · exact N6.BranchEval.B3.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h3
  · exact N6.BranchEval.B4.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h4
  · exact N6.BranchEval.B5.ProgramData.scaled_maximum_impossible hz hα hA b c d e hb hp h5

#print axioms generic_scaled_maximum_impossible
end N6.BranchEval

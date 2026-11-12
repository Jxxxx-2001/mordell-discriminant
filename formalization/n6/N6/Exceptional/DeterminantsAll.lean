import N6.Exceptional.Determinants007
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
theorem presentation_full_jet (b c d e U : ℂ) :
    (N6.Resultant6General.presentation 0 b c d e U 0).det = value (point b c d e U) D063 ∧
    HasDerivAt (fun T : ℂ => (N6.Resultant6General.presentation 0 b c d e U T).det) (value (point b c d e U) J063) 0 := by
  exact detJet063 b c d e U
theorem stationaryResultant_full_jet (w : N6.Configuration) (hw : Function.Injective w)
    (b c d e U : ℂ) (hp : N6.rootPolynomial w = N6.coefficientSextic 0 b c d e) :
    N6.stationaryResultant w U 0 = value (point b c d e U) D063 ∧
    HasDerivAt (fun T : ℂ => N6.stationaryResultant w U T) (value (point b c d e U) J063) 0 := by
  have full := presentation_full_jet b c d e U
  constructor
  · exact (N6.Resultant6General.stationaryResultant_eq_det w hw 0 b c d e U 0 hp).trans full.1
  · have he : (fun T : ℂ => N6.stationaryResultant w U T) = (fun T : ℂ => (N6.Resultant6General.presentation 0 b c d e U T).det) := by
      funext T
      exact N6.Resultant6General.stationaryResultant_eq_det w hw 0 b c d e U T hp
    rw [he]
    exact full.2
#print axioms stationaryResultant_full_jet
end N6.Exceptional

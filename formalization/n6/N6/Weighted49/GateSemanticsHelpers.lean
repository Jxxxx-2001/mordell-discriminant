import N6.Weighted49.Columns
import N6.Weighted49.LinearSemantics
import N6.Weighted49.VecData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_gate {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (M : Fin 49 → Fin 49 → Int) (G a b ds dt : Int) (y : R)
    (src dst : Fin 49 → Int) (ms md mv : Mon)
    (ha : a ≠ 0) (scaleEq : a*dt = b*G*ds)
    (vecEq : ∀ i, a*dst i = b*matVec M src i)
    (columns : ∀ j, (G : R)*y*value x (basisData j) = W (fun i => value x (basisData i)) (fun i => M i j))
    (source : W (fun i => value x (basisData i)) src = (ds : R)*monVal x ms)
    (hm : md = ms.plus mv) (hv : monVal x mv = y) :
    W (fun i => value x (basisData i)) dst = (dt : R)*monVal x md := by
  have h := action_gate (fun i => value x (basisData i)) M G a b ds dt y (monVal x ms) src dst ha scaleEq vecEq columns source
  rw [h, hm, monVal_plus, hv]
  ring
end N6.Weighted49

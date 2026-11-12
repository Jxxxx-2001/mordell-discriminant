import N6.Weighted49.ActionSemantics
import N6.Weighted49.ParentsFromInputs
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem all_actions_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : ∀ i : Fin 49, value x (actionData i) = 0 :=
  all_actions_vanish x (parents_from_inputs x h0 h1 h2 h3 hs)
#print axioms all_actions_from_inputs
end N6.Weighted49

import N6.ResultantMinors.Data
import review.SparseCheck
import review.Resultant6Matrix
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck
def point {R : Type*} (b c d e U : R) : Fin 5 → R := ![U,e,d,c,b]
@[simp] theorem point_eval0 {R : Type*} (b c d e U : R) : point b c d e U 0 = U := rfl
@[simp] theorem point_eval1 {R : Type*} (b c d e U : R) : point b c d e U 1 = e := rfl
@[simp] theorem point_eval2 {R : Type*} (b c d e U : R) : point b c d e U 2 = d := rfl
@[simp] theorem point_eval3 {R : Type*} (b c d e U : R) : point b c d e U 3 = c := rfl
@[simp] theorem point_eval4 {R : Type*} (b c d e U : R) : point b c d e U 4 = b := rfl
def entryA : Fin 6 → Fin 6 → Poly := ![![A00, A01, A02, A03, A04, A05], ![A10, A11, A12, A13, A14, A15], ![A20, A21, A22, A23, A24, A25], ![A30, A31, A32, A33, A34, A35], ![A40, A41, A42, A43, A44, A45], ![A50, A51, A52, A53, A54, A55]]
def entryH : Fin 6 → Fin 6 → Poly := ![![H00, H01, H02, H03, H04, H05], ![H10, H11, H12, H13, H14, H15], ![H20, H21, H22, H23, H24, H25], ![H30, H31, H32, H33, H34, H35], ![H40, H41, H42, H43, H44, H45], ![H50, H51, H52, H53, H54, H55]]
private theorem presentation_column0 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 0 =
      value (point b c d e U) (entryA i 0) + T*value (point b c d e U) (entryH i 0) := by
  fin_cases i
  · change (U*d-2*c-6*e*T) = value (point b c d e U) A00 +
      T*value (point b c d e U) H00
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A00, A00Part0, H00, H00Part0, m0007, m0070, m0170] <;> ring
  · change (2*c*U-6*b-5*d*T) = value (point b c d e U) A10 +
      T*value (point b c d e U) H10
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A10, A10Part0, H10, H10Part0, m0001, m0029, m0145] <;> ring
  · change (3*b*U-12-4*c*T) = value (point b c d e U) A20 +
      T*value (point b c d e U) H20
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A20, A20Part0, H20, H20Part0, m0000, m0007, m0138] <;> ring
  · change (4*U-3*b*T) = value (point b c d e U) A30 +
      T*value (point b c d e U) H30
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A30, A30Part0, H30, H30Part0, m0001, m0137] <;> ring
  · change (-30-2*T) = value (point b c d e U) A40 +
      T*value (point b c d e U) H40
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A40, A40Part0, H40, H40Part0, m0000] <;> ring
  · change (6*U) = value (point b c d e U) A50 +
      T*value (point b c d e U) H50
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A50, A50Part0, H50, m0137] <;> ring
private theorem presentation_column1 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 1 =
      value (point b c d e U) (entryA i 1) + T*value (point b c d e U) (entryH i 1) := by
  fin_cases i
  · change (-e*(6*U)) = value (point b c d e U) A01 +
      T*value (point b c d e U) H01
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A01, A01Part0, H01, m0222] <;> ring
  · change ((U*d-2*c-6*e*T)-d*(6*U)) = value (point b c d e U) A11 +
      T*value (point b c d e U) H11
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A11, A11Part0, H11, H11Part0, m0007, m0070, m0170] <;> ring
  · change ((2*c*U-6*b-5*d*T)-c*(6*U)) = value (point b c d e U) A21 +
      T*value (point b c d e U) H21
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A21, A21Part0, H21, H21Part0, m0001, m0029, m0145] <;> ring
  · change ((3*b*U-12-4*c*T)-b*(6*U)) = value (point b c d e U) A31 +
      T*value (point b c d e U) H31
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A31, A31Part0, H31, H31Part0, m0000, m0007, m0138] <;> ring
  · change ((4*U-3*b*T)-(6*U)) = value (point b c d e U) A41 +
      T*value (point b c d e U) H41
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A41, A41Part0, H41, H41Part0, m0001, m0137] <;> ring
  · change ((-30-2*T)) = value (point b c d e U) A51 +
      T*value (point b c d e U) H51
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A51, A51Part0, H51, H51Part0, m0000] <;> ring
private theorem presentation_column2 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 2 =
      value (point b c d e U) (entryA i 2) + T*value (point b c d e U) (entryH i 2) := by
  fin_cases i
  · change (-e*((-30-2*T))) = value (point b c d e U) A02 +
      T*value (point b c d e U) H02
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A02, A02Part0, H02, H02Part0, m0070] <;> ring
  · change ((-e*(6*U))-d*((-30-2*T))) = value (point b c d e U) A12 +
      T*value (point b c d e U) H12
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A12, A12Part0, H12, H12Part0, m0029, m0222] <;> ring
  · change (((U*d-2*c-6*e*T)-d*(6*U))-c*((-30-2*T))) = value (point b c d e U) A22 +
      T*value (point b c d e U) H22
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A22, A22Part0, H22, H22Part0, m0007, m0070, m0170] <;> ring
  · change (((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T))) = value (point b c d e U) A32 +
      T*value (point b c d e U) H32
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A32, A32Part0, H32, H32Part0, m0001, m0029, m0145] <;> ring
  · change (((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))) = value (point b c d e U) A42 +
      T*value (point b c d e U) H42
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A42, A42Part0, H42, H42Part0, m0000, m0007, m0138] <;> ring
  · change (((4*U-3*b*T)-(6*U))) = value (point b c d e U) A52 +
      T*value (point b c d e U) H52
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A52, A52Part0, H52, H52Part0, m0001, m0137] <;> ring
private theorem presentation_column3 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 3 =
      value (point b c d e U) (entryA i 3) + T*value (point b c d e U) (entryH i 3) := by
  fin_cases i
  · change (-e*(((4*U-3*b*T)-(6*U)))) = value (point b c d e U) A03 +
      T*value (point b c d e U) H03
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A03, A03Part0, H03, H03Part0, m0071, m0222] <;> ring
  · change ((-e*((-30-2*T)))-d*(((4*U-3*b*T)-(6*U)))) = value (point b c d e U) A13 +
      T*value (point b c d e U) H13
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A13, A13Part0, H13, H13Part0, m0030, m0070, m0170] <;> ring
  · change (((-e*(6*U))-d*((-30-2*T)))-c*(((4*U-3*b*T)-(6*U)))) = value (point b c d e U) A23 +
      T*value (point b c d e U) H23
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A23, A23Part0, H23, H23Part0, m0008, m0029, m0145, m0222] <;> ring
  · change ((((U*d-2*c-6*e*T)-d*(6*U))-c*((-30-2*T)))-b*(((4*U-3*b*T)-(6*U)))) = value (point b c d e U) A33 +
      T*value (point b c d e U) H33
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A33, A33Part0, H33, H33Part0, m0002, m0007, m0070, m0138, m0170] <;> ring
  · change ((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))) = value (point b c d e U) A43 +
      T*value (point b c d e U) H43
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A43, A43Part0, H43, H43Part0, m0001, m0029, m0137, m0145] <;> ring
  · change ((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))) = value (point b c d e U) A53 +
      T*value (point b c d e U) H53
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A53, A53Part0, H53, H53Part0, m0000, m0007, m0138] <;> ring
private theorem presentation_column4 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 4 =
      value (point b c d e U) (entryA i 4) + T*value (point b c d e U) (entryH i 4) := by
  fin_cases i
  · change (-e*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))))) = value (point b c d e U) A04 +
      T*value (point b c d e U) H04
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A04, A04Part0, H04, H04Part0, m0070, m0077, m0223] <;> ring
  · change ((-e*(((4*U-3*b*T)-(6*U))))-d*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))))) = value (point b c d e U) A14 +
      T*value (point b c d e U) H14
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A14, A14Part0, H14, H14Part0, m0029, m0035, m0071, m0171, m0222] <;> ring
  · change (((-e*((-30-2*T)))-d*(((4*U-3*b*T)-(6*U))))-c*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))))) = value (point b c d e U) A24 +
      T*value (point b c d e U) H24
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A24, A24Part0, H24, H24Part0, m0007, m0013, m0030, m0070, m0146, m0170] <;> ring
  · change ((((-e*(6*U))-d*((-30-2*T)))-c*(((4*U-3*b*T)-(6*U))))-b*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))))) = value (point b c d e U) A34 +
      T*value (point b c d e U) H34
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A34, A34Part0, H34, H34Part0, m0001, m0008, m0029, m0139, m0145, m0222] <;> ring
  · change (((((U*d-2*c-6*e*T)-d*(6*U))-c*((-30-2*T)))-b*(((4*U-3*b*T)-(6*U))))-((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T))))) = value (point b c d e U) A44 +
      T*value (point b c d e U) H44
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A44, A44Part0, H44, H44Part0, m0000, m0002, m0007, m0070, m0138, m0170] <;> ring
  · change (((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U))))) = value (point b c d e U) A54 +
      T*value (point b c d e U) H54
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A54, A54Part0, H54, H54Part0, m0001, m0029, m0137, m0145] <;> ring
private theorem presentation_column5 (b c d e U T : ℂ) (i : Fin 6) :
    N6.Resultant6.presentation b c d e U T i 5 =
      value (point b c d e U) (entryA i 5) + T*value (point b c d e U) (entryH i 5) := by
  fin_cases i
  · change (-e*(((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))))) = value (point b c d e U) A05 +
      T*value (point b c d e U) H05
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A05, A05Part0, H05, H05Part0, m0071, m0091, m0222, m0229] <;> ring
  · change ((-e*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))))-d*(((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))))) = value (point b c d e U) A15 +
      T*value (point b c d e U) H15
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A15, A15Part0, H15, H15Part0, m0030, m0050, m0070, m0077, m0170, m0177, m0223] <;> ring
  · change (((-e*(((4*U-3*b*T)-(6*U))))-d*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))))-c*(((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))))) = value (point b c d e U) A25 +
      T*value (point b c d e U) H25
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A25, A25Part0, H25, H25Part0, m0008, m0029, m0035, m0071, m0145, m0152, m0171, m0222] <;> ring
  · change ((((-e*((-30-2*T)))-d*(((4*U-3*b*T)-(6*U))))-c*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))))-b*(((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))))) = value (point b c d e U) A35 +
      T*value (point b c d e U) H35
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A35, A35Part0, H35, H35Part0, m0002, m0007, m0013, m0030, m0070, m0138, m0146, m0170] <;> ring
  · change (((((-e*(6*U))-d*((-30-2*T)))-c*(((4*U-3*b*T)-(6*U))))-b*((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))))-(((((2*c*U-6*b-5*d*T)-c*(6*U))-b*((-30-2*T)))-(((4*U-3*b*T)-(6*U)))))) = value (point b c d e U) A45 +
      T*value (point b c d e U) H45
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A45, A45Part0, H45, H45Part0, m0001, m0008, m0029, m0137, m0139, m0145, m0222] <;> ring
  · change ((((((U*d-2*c-6*e*T)-d*(6*U))-c*((-30-2*T)))-b*(((4*U-3*b*T)-(6*U))))-((((3*b*U-12-4*c*T)-b*(6*U))-((-30-2*T)))))) = value (point b c d e U) A55 +
      T*value (point b c d e U) H55
    norm_num [value, monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, A55, A55Part0, H55, H55Part0, m0000, m0002, m0007, m0070, m0138, m0170] <;> ring
theorem presentation_entry (b c d e U T : ℂ) (i j : Fin 6) :
    N6.Resultant6.presentation b c d e U T i j =
      value (point b c d e U) (entryA i j) + T*value (point b c d e U) (entryH i j) := by
  fin_cases j
  · exact presentation_column0 b c d e U T i
  · exact presentation_column1 b c d e U T i
  · exact presentation_column2 b c d e U T i
  · exact presentation_column3 b c d e U T i
  · exact presentation_column4 b c d e U T i
  · exact presentation_column5 b c d e U T i
theorem presentation_entry_zero (b c d e U : ℂ) (i j : Fin 6) :
    N6.Resultant6.presentation b c d e U 0 i j = value (point b c d e U) (entryA i j) := by
  rw [presentation_entry]; ring
theorem presentation_entry_hasDerivAt (b c d e U : ℂ) (i j : Fin 6) :
    HasDerivAt (fun T : ℂ => N6.Resultant6.presentation b c d e U T i j)
      (value (point b c d e U) (entryH i j)) 0 := by
  have he : (fun T : ℂ => N6.Resultant6.presentation b c d e U T i j) =
      (fun T : ℂ => value (point b c d e U) (entryA i j) +
        T*value (point b c d e U) (entryH i j)) := by
    funext T; exact presentation_entry b c d e U T i j
  rw [he]
  simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (value (point b c d e U) (entryH i j))).const_add
    (value (point b c d e U) (entryA i j))
#print axioms presentation_entry
#print axioms presentation_entry_hasDerivAt
end N6.ResultantMinors

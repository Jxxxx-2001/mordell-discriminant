import Eight.OuterContact.C2.Matrix
import Eight.KernelBridge

namespace MordellEight.OuterContact.C2
open Checks Matrix Set GapAnalytic
set_option maxHeartbeats 0
attribute [local irreducible] exactMajorant
theorem polynomial_real (i j : Fin 3) (x : Fin 3 → ℝ) :
    (polynomials i j).real (x 0-1) (x 1-1) (x 2-(q:ℝ))=
      eval3 (partialPoly (partialPoly exactMajorant i) j) x := by
  have h00 := H00.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  have h01 := H01.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  have h02 := H02.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  have h11 := H11.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  have h12 := H12.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  have h22 := H22.polynomial_real (x 0-1) (x 1-1) (x 2-(q:ℝ))
  simp only [q,sub_add_cancel] at h00 h01 h02 h11 h12 h22
  have h10 := mixed_partials exactMajorant (0:Fin 3) 1 x
  have h20 := mixed_partials exactMajorant (0:Fin 3) 2 x
  have h21 := mixed_partials exactMajorant (1:Fin 3) 2 x
  fin_cases i <;> fin_cases j
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h00
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h01
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h02
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h01.trans h10
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h11
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h12
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h02.trans h20
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h12.trans h21
  · simpa [q,polynomials,partialPoly,eval3,Matrix.cons_val_two] using h22

theorem cube_hessian_posDef {x : Fin 3 → ℝ} (hx : InCube q radius x) :
    (hessian exactMajorant x).PosDef :=
  intervalMatrixCheck_sound bounds C U R D error checked _
    (hessian_isHermitian exactMajorant x)
    (hessian_bounds_sound distance_min_pos polynomials polynomial_real hx)

theorem majorant {x : Fin 3 → ℝ} (hx : InCube q radius x) :
    Real.log (x 0+x 1-2*x 2)≤majorantFromMatrices (x 0) (x 1) (x 2) := by
  rw [←exact_majorant_eq_kernel]
  exact cube_gap_nonneg 2 (by decide) distance_min_pos contact_check (fun _ => cube_hessian_posDef) hx
end MordellEight.OuterContact.C2

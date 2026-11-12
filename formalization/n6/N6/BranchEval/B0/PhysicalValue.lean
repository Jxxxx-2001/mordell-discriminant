import N6.BranchEval.B0.Complete
import N6.BranchEval.RealValues
import N6.Univariate.Branch0

set_option autoImplicit false

namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.BranchEval.Program

theorem Di_onlyB : N6.BranchEval.onlyB input4NF.num = true := by decide +kernel

/-- A physical point of the actual saturated chart has the checked real value.
No root count, coordinate recovery assumption, or certificate-success premise is used. -/
theorem physical_value (x : Fin 5 → ℂ) (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 225)
    (hf : value x program.factor = 0)
    (hc : N6.Weighted49.coordinate_c (x 4) (x 3) = 0)
    (hk : N6.Weighted49.coordinate_k (x 4) (x 2) = 0)
    (he : N6.Weighted49.coordinate_e (x 4) (x 1) = 0)
    (hd : originalD (x 4) (x 3) (x 2) (x 1) ≠ 0)
    (hphysical : originalR4 (x 4) (x 3) (x 2) (x 1) =
      originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ)) :
    ∃ D V : ℝ, originalD (x 4) (x 3) (x 2) (x 1) = (D : ℂ) ∧
      V = a^15*D^2/(5 : ℝ)^30 ∧ V < (6 : ℝ)^12 := by
  obtain ⟨hD,hR,hDR,hH,hB,hV⟩ := endpoints_from_coordinates x hf hc hk he
  have hDi : Di x ≠ 0 := by rwa [← hD]
  have hay : Ay x = (a : ℂ) := by
    apply mul_left_cancel₀ hDi
    calc
      Di x * Ay x = Ri x := hDR
      _ = originalR4 (x 4) (x 3) (x 2) (x 1) := hR.symm
      _ = originalD (x 4) (x 3) (x 2) (x 1) * (a : ℂ) := hphysical
      _ = Di x * (a : ℂ) := by rw [hD]
  rw [hay] at hH hB hV
  have hHcast : H (a : ℂ) = (H (K := ℝ) a : ℂ) :=
    N6.BranchEval.ratEval_ofReal hCoefficients a
  have hBcast : B_from_Ay (a : ℂ) = (B_from_Ay (K := ℝ) a : ℂ) :=
    N6.BranchEval.ratEval_ofReal bCoefficients a
  have hVcast : V (a : ℂ) = (V (K := ℝ) a : ℂ) :=
    N6.BranchEval.ratEval_ofReal vCoefficients a
  have hroot : N6.Univariate.eval N6.Univariate.Branch0.p a = 0 := by
    rw [hHcast] at hH
    rw [← H_real_published]
    exact Complex.ofReal_injective hH
  have bound := (N6.Univariate.Branch0.root_value_bound a ha hroot).2
  let Dreal : ℝ := N6.BranchEval.realNF (B_from_Ay a) input4NF
  have hDreal : Di x = (Dreal : ℂ) :=
    N6.BranchEval.meaning_of_real_B x input4NF (B_from_Ay a) Di_onlyB
      (hB.symm.trans hBcast)
  have hval : (V (K := ℝ) a : ℂ) = ((a^15*Dreal^2/(5 : ℝ)^30 : ℝ) : ℂ) := by
    rw [hVcast, hDreal] at hV
    simpa only [physicalSquare, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_ofNat] using hV
  refine ⟨Dreal, V a, hD.trans hDreal, Complex.ofReal_injective hval, ?_⟩
  simpa only [V_real_published] using bound

#print axioms physical_value
end N6.BranchEval.B0.ProgramData

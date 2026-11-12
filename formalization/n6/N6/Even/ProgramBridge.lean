import N6.Even.ProgramSemantics
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace N6.Even.ProgramData
open N6.SparseCheck N6.BranchEval.Program

variable {K : Type*} [Field K] [CharZero K]

theorem factor_value (x : Fin 5 → K) : value x program.factor = N6.Even.p6 (x 4) := by
  simp [program, factorData, factorDataPart0, value, monVal, pm0, pm1, pm2,
    pm3, pm4, pm5, pm6, N6.Even.p6] <;> ring

theorem C_value (x : Fin 5 → K) : C x = x 4 := by
  apply input_of_projection x input0NF (x 4) input0_den_ne_zero
  simp [input0NF, input0Num, input0NumPart0, value, monVal, pm1]

theorem E_value (x : Fin 5 → K) : E x = N6.Even.eGraph (x 4)/180 := by
  apply input_of_projection x input1NF (N6.Even.eGraph (x 4)/180) input1_den_ne_zero
  simp [input1NF, input1Num, input1NumPart0, value, monVal, pm0, pm1, pm2,
    pm3, pm4, pm5, N6.Even.eGraph] <;> field_simp <;> ring

theorem E_from_graph (x : Fin 5 → K) (e : K)
    (he : 180*e-N6.Even.eGraph (x 4)=0) : E x = e := by
  rw [E_value]
  apply (div_eq_iff (by norm_num : (180 : K) ≠ 0)).mpr
  linear_combination -he

/-- All computation is discharged by checked_program, not retained as a hypothesis. -/
theorem endpoints_from_graph (c e : K) (hp : N6.Even.p6 c=0)
    (he : 180*e-N6.Even.eGraph c=0) :
    actualD c e*A c=actualR4 c e ∧
    actualD c e*actualR02 c e=c*(actualR4 c e)^2 ∧
    V c=(A c)^15*(actualD c e)^2/(5^30 : K) := by
  have hx : pointC c 4 = c := by rfl
  have hf : value (pointC c) program.factor=0 := by rw [factor_value,hx,hp]
  have hc : C (pointC c)=c := (C_value _).trans hx
  have hE : E (pointC c)=e := E_from_graph _ e (by simpa only [hx] using he)
  have h0 := endpoint0 (pointC c) hf
  have h1 := endpoint1 (pointC c) hf
  rw [hc,hE] at h0 h1
  have h3 := endpoint3 (pointC c) hf
  rw [←h0,←h1] at h3
  have h4 := endpoint4 (pointC c) hf
  rw [hc,hE] at h4
  have h5 := endpoint5 (pointC c) hf
  rw [←h0] at h5
  exact ⟨by simpa only [A] using h3,h4,by simpa only [A,V] using h5⟩

theorem actualD_chart (c e : K) : actualD c e = N6.Chart.originalD 0 c 0 e := by
  simp [actualD,N6.Chart.originalD] <;> ring

theorem endpoints_from_raw [Algebra ℚ K] (c e : K)
    (h1 : N6.Chart.E1 0 c 0 e=0) (h3 : N6.Chart.E3 0 c 0 e=0)
    (hd : N6.Chart.originalD 0 c 0 e ≠ 0) :
    actualD c e*A c=actualR4 c e ∧
    actualD c e*actualR02 c e=c*(actualR4 c e)^2 ∧
    V c=(A c)^15*(actualD c e)^2/(5^30 : K) := by
  obtain ⟨hp,he⟩ := N6.Even.coverage_of_raw c e h1 h3 hd
  exact endpoints_from_graph c e hp he

theorem p6_ofReal (c : ℝ) : N6.Even.p6 (K := ℂ) (c : ℂ) = ((N6.Even.p6 (K := ℝ) c : ℝ) : ℂ) := by
  simp [N6.Even.p6]

theorem eGraph_ofReal (c : ℝ) : N6.Even.eGraph (K := ℂ) (c : ℂ) = ((N6.Even.eGraph (K := ℝ) c : ℝ) : ℂ) := by
  simp [N6.Even.eGraph]

theorem actualD_ofReal (c e : ℝ) : actualD (K := ℂ) (c : ℂ) (e : ℂ) = ((actualD (K := ℝ) c e : ℝ) : ℂ) := by
  simp [actualD]

theorem actualR4_ofReal (c e : ℝ) : actualR4 (K := ℂ) (c : ℂ) (e : ℂ) = ((actualR4 (K := ℝ) c e : ℝ) : ℂ) := by
  simp [actualR4]

/-- The exact coefficient identity forces c to be real on the physical branch. -/
theorem c_im_zero_from_dual_coefficients {D r4 r02 c : ℂ} {a : ℝ}
    (hd : D ≠ 0) (ha : 0<a) (hid : D*r02=c*r4^2)
    (h4 : r4=D*(a : ℂ)) (h2 : r02=D*star c*(a : ℂ)^2) : c.im=0 := by
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  rw [h4,h2] at hid
  have hz : (star c-c)*(D^2*(a : ℂ)^2)=0 := by linear_combination hid
  have hn : D^2*(a : ℂ)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hd) (pow_ne_zero _ ha0)
  have hc : star c=c := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def,Complex.conj_im] at hi
  linarith

theorem c_real_of_physical (c e : ℂ) (a : ℝ) (hp : N6.Even.p6 c=0)
    (he : 180*e-N6.Even.eGraph c=0) (hd : actualD c e ≠ 0) (ha : 0<a)
    (h4 : actualR4 c e=actualD c e*(a : ℂ))
    (h2 : actualR02 c e=actualD c e*star c*(a : ℂ)^2) : c=(c.re : ℂ) := by
  have hid := (endpoints_from_graph c e hp he).2.1
  have hi := c_im_zero_from_dual_coefficients hd ha hid h4 h2
  apply Complex.ext
  · simp
  · simpa using hi

#print axioms endpoints_from_raw
#print axioms c_real_of_physical
end N6.Even.ProgramData

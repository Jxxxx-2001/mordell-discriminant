import Mathlib.Topology.Order.IntermediateValue
import Eight.Checks.LogBounds
import Mathlib.Tactic

namespace MordellEight

def cubic (x : ℝ) : ℝ := 8*x^3+4*x^2-4*x-1
def alphaLo : ℚ := 6234898018/10000000000
def alphaHi : ℚ := 6234898019/10000000000

theorem root_exists : ∃ a : ℝ, (alphaLo : ℝ) ≤ a ∧ a ≤ (alphaHi : ℝ) ∧ cubic a = 0 := by
  have hc : Continuous cubic := by unfold cubic; fun_prop
  have hl : cubic (alphaLo : ℝ) ≤ 0 := by norm_num [cubic, alphaLo]
  have hu : 0 ≤ cubic (alphaHi : ℝ) := by norm_num [cubic, alphaHi]
  obtain ⟨a, ha, he⟩ := intermediate_value_Icc
    (show (alphaLo : ℝ) ≤ (alphaHi : ℝ) by norm_num [alphaLo,alphaHi]) hc.continuousOn ⟨hl,hu⟩
  exact ⟨a,ha.1,ha.2,he⟩

noncomputable def alpha : ℝ := Classical.choose root_exists
theorem alpha_bounds : (alphaLo : ℝ) ≤ alpha ∧ alpha ≤ (alphaHi : ℝ) :=
  ⟨(Classical.choose_spec root_exists).1,(Classical.choose_spec root_exists).2.1⟩
theorem alpha_equation : cubic alpha = 0 := (Classical.choose_spec root_exists).2.2
theorem alpha_coarse : (1/2:ℝ) < alpha ∧ alpha < 5/8 := by
  have h := alpha_bounds
  norm_num [alphaLo,alphaHi] at h
  constructor <;> linarith

theorem cubic_strict {x y : ℝ} (hx : 1/2 ≤ x) (hxy : x < y) : cubic x < cubic y := by
  have hy : (1/2:ℝ) ≤ y := le_trans hx hxy.le
  have hx2 : (1/4:ℝ) ≤ x^2 := by nlinarith
  have hy2 : (1/4:ℝ) ≤ y^2 := by nlinarith
  have hprod : (1/4:ℝ) ≤ x*y := by
    have h := mul_le_mul hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by linarith : 0 ≤ x)
    nlinarith
  have hfactor : 0 < 8*(y^2+x*y+x^2)+4*(y+x)-4 := by linarith
  have hp := mul_pos (sub_pos.mpr hxy) hfactor
  have he : cubic y-cubic x = (y-x)*(8*(y^2+x*y+x^2)+4*(y+x)-4) := by
    unfold cubic
    ring
  linarith

theorem alpha_unique {a : ℝ} (ha : (1/2:ℝ) ≤ a) (hz : cubic a = 0) : a = alpha := by
  rcases lt_trichotomy a alpha with h | h | h
  · have hc := cubic_strict ha h
    rw [hz,alpha_equation] at hc
    exact (lt_irrefl _ hc).elim
  · exact h
  · have hc := cubic_strict alpha_coarse.1.le h
    rw [hz,alpha_equation] at hc
    exact (lt_irrefl _ hc).elim

/-- The algebraic representation is fixed by its polynomial and isolating interval.
No unproved trigonometric identity is needed to define the auxiliary kernel. -/
noncomputable def cosineValues : Fin 3 → ℝ :=
  ![alpha, 2*alpha^2-1, -2*alpha^2-alpha+1/2]
noncomputable def distanceParameters : Fin 3 → ℝ := fun j => 2-2*cosineValues j
noncomputable def logConstants : Fin 3 → ℝ := fun j => Real.log (distanceParameters j)

/-- Coordinates in Q(alpha) are represented explicitly, without a floating-point embedding. -/
abbrev AlgebraicCoeff := Fin 3 → ℚ
noncomputable def AlgebraicCoeff.real (a : AlgebraicCoeff) : ℝ :=
  (a 0:ℝ)+(a 1:ℝ)*alpha+(a 2:ℝ)*alpha^2
abbrev KernelCoeff := Fin 4 → AlgebraicCoeff
noncomputable def KernelCoeff.real (a : KernelCoeff) : ℝ :=
  (a 0).real + ∑ j : Fin 3, (a j.succ).real * logConstants j

end MordellEight

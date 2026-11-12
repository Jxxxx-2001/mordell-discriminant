import N6.Even.ProgramBridge
import N6.Even.ValueBound

set_option autoImplicit false
namespace N6.Even.ProgramData

theorem physical_value_bound_real (c e a : ℝ) (hp : N6.Even.p6 (K := ℝ) c=0)
    (he : 180*e-N6.Even.eGraph (K := ℝ) c=0) (hd : actualD (K := ℝ) c e ≠ 0)
    (h4 : actualR4 (K := ℝ) c e=actualD (K := ℝ) c e*a) :
    a^15*(actualD (K := ℝ) c e)^2/(5^30 : ℝ) < (6 : ℝ)^12 := by
  have h := endpoints_from_graph (K := ℝ) c e hp he
  have hA : A (K := ℝ) c=a := by
    have hrel := h.1
    rw [h4] at hrel
    exact mul_left_cancel₀ hd hrel
  have hv := h.2.2
  rw [hA] at hv
  rw [←hv]
  exact (N6.Even.ValueCover.root_value_bound c hp).2

/-- A real interval theorem applied only after the exact physical realness step. -/
theorem physical_value_bound (c e : ℂ) (a : ℝ) (hp : N6.Even.p6 c=0)
    (he : 180*e-N6.Even.eGraph c=0) (hd : actualD c e ≠ 0) (ha : 0<a)
    (h4 : actualR4 c e=actualD c e*(a : ℂ))
    (h2 : actualR02 c e=actualD c e*star c*(a : ℂ)^2) :
    a^15*Complex.normSq (actualD c e)/(5^30 : ℝ) < (6 : ℝ)^12 := by
  let cr : ℝ := c.re
  let er : ℝ := N6.Even.eGraph (K := ℝ) cr/180
  have hc : c=(cr : ℂ) := c_real_of_physical c e a hp he hd ha h4 h2
  have heq : e=N6.Even.eGraph c/(180 : ℂ) := by
    apply (eq_div_iff (by norm_num : (180 : ℂ) ≠ 0)).mpr
    linear_combination he
  rw [hc,eGraph_ofReal] at heq
  have hE : e=(er : ℂ) := by simpa [er] using heq
  have hpR : N6.Even.p6 (K := ℝ) cr=0 := by
    apply Complex.ofReal_injective
    simpa only [hc,p6_ofReal,Complex.ofReal_zero] using hp
  have heR : 180*er-N6.Even.eGraph (K := ℝ) cr=0 := by
    dsimp [er]
    field_simp <;> ring
  have hD : actualD (K := ℂ) c e=((actualD (K := ℝ) cr er : ℝ) : ℂ) := by rw [hc,hE,actualD_ofReal]
  have hdR : actualD (K := ℝ) cr er ≠ 0 := by
    intro hz
    apply hd
    rw [hD,hz,Complex.ofReal_zero]
  have h4R : actualR4 (K := ℝ) cr er=actualD (K := ℝ) cr er*a := by
    apply Complex.ofReal_injective
    simpa only [hc,hE,actualR4_ofReal,actualD_ofReal,Complex.ofReal_mul] using h4
  have hv := physical_value_bound_real cr er a hpR heR hdR h4R
  rw [hD,Complex.normSq_ofReal]
  simpa only [pow_two] using hv

theorem physical_value_bound_from_raw (c e : ℂ) (a : ℝ)
    (h1 : N6.Chart.E1 0 c 0 e=0) (h3 : N6.Chart.E3 0 c 0 e=0)
    (hd : N6.Chart.originalD 0 c 0 e ≠ 0) (ha : 0<a)
    (h4 : actualR4 c e=actualD c e*(a : ℂ))
    (h2 : actualR02 c e=actualD c e*star c*(a : ℂ)^2) :
    a^15*Complex.normSq (actualD c e)/(5^30 : ℝ) < (6 : ℝ)^12 := by
  obtain ⟨hp,he⟩ := N6.Even.coverage_of_raw c e h1 h3 hd
  apply physical_value_bound c e a hp he ?_ ha h4 h2
  simpa only [actualD_chart] using hd

#print axioms physical_value_bound_from_raw
end N6.Even.ProgramData

import N6.Analysis.MaximumClassification
import N6.Pentagon.Witness

set_option autoImplicit false

namespace N6

theorem mordell_six_sharp_bound (z : Fin 6 → ℂ) (hz : normSum z = 6) :
    discriminant z ≤ (6 : ℝ)^15 / 5^10 := by
  obtain ⟨w,hw,_,_⟩ := exists_centered_distinct_global_maximum
  have he := (Pentagon.centeredPentagon_sharp (global_maximum_classification hw)).2
  exact (hw.2 z hz).trans_eq he

theorem mordell_six_equality_iff (z : Fin 6 → ℂ) (hz : normSum z = 6) :
    discriminant z = (6 : ℝ)^15 / 5^10 ↔ IsCenteredPentagon z := by
  constructor
  · intro he
    apply global_maximum_classification
    refine ⟨hz, ?_⟩
    intro w hw
    rw [he]
    exact mordell_six_sharp_bound w hw
  · intro hs
    exact (Pentagon.centeredPentagon_sharp hs).2

theorem mordell_six_sharp_witness :
    normSum Pentagon.sharpWitness = 6 ∧
      discriminant Pentagon.sharpWitness = (6 : ℝ)^15 / 5^10 :=
  ⟨Pentagon.sharpWitness_normSum, Pentagon.sharpWitness_discriminant⟩

theorem mordell_six_norm_bound (z : Fin 6 → ℂ) (hz : ∑ i, ‖z i‖^2 = 6) :
    (∏ p ∈ (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2)),
      ‖z p.1-z p.2‖^2) ≤ (6 : ℝ)^15/5^10 := by
  have hn : normSum z = 6 := by
    simpa only [normSum, Complex.normSq_eq_norm_sq] using hz
  simpa only [discriminant, pairs, Complex.normSq_eq_norm_sq] using
    mordell_six_sharp_bound z hn

theorem mordell_six_norm_equality_iff (z : Fin 6 → ℂ) (hz : ∑ i, ‖z i‖^2 = 6) :
    (∏ p ∈ (Finset.univ.filter (fun p : Fin 6 × Fin 6 => p.1 < p.2)),
      ‖z p.1-z p.2‖^2) = (6 : ℝ)^15/5^10 ↔ IsCenteredPentagon z := by
  have hn : normSum z = 6 := by
    simpa only [normSum, Complex.normSq_eq_norm_sq] using hz
  simpa only [discriminant, pairs, Complex.normSq_eq_norm_sq] using
    mordell_six_equality_iff z hn

#print axioms mordell_six_sharp_bound
#print axioms mordell_six_equality_iff
#print axioms mordell_six_sharp_witness
#print axioms mordell_six_norm_bound
#print axioms mordell_six_norm_equality_iff
end N6

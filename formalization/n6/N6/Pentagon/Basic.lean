import N6.Analysis.Normalization
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

namespace N6

/-- A zero center followed by a rotated and scaled regular pentagon. -/
noncomputable def pentagonConfiguration (u ω : ℂ) : Configuration :=
  Fin.cases 0 (fun j : Fin 5 => u * ω^j.val)

namespace Pentagon

theorem primitive_normSq {ω : ℂ} (hω : IsPrimitiveRoot ω 5) : Complex.normSq ω = 1 := by
  rw [Complex.normSq_eq_norm_sq, hω.norm'_eq_one (by decide)]
  norm_num

theorem primitive_power_normSq {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (k : ℕ) :
    Complex.normSq (ω^k) = 1 := by
  rw [map_pow, primitive_normSq hω, one_pow]

theorem normSq_sub_comm (a b : ℂ) : Complex.normSq (a-b) = Complex.normSq (b-a) := by
  rw [← Complex.normSq_neg (a-b)]
  congr 1
  ring

theorem primitive_distance {ω : ℂ} (hω : IsPrimitiveRoot ω 5)
    (i j : ℕ) (hij : i ≤ j) :
    Complex.normSq (ω^i-ω^j) = Complex.normSq (1-ω^(j-i)) := by
  have hpow : ω^j = ω^i * ω^(j-i) := by rw [← pow_add, Nat.add_sub_of_le hij]
  rw [hpow]
  have he : ω^i - ω^i*ω^(j-i) = ω^i*(1-ω^(j-i)) := by ring
  rw [he, Complex.normSq_mul, primitive_power_normSq hω, one_mul]

theorem primitive_distance_complement {ω : ℂ} (hω : IsPrimitiveRoot ω 5)
    (k : ℕ) (hk : k ≤ 5) :
    Complex.normSq (1-ω^(5-k)) = Complex.normSq (1-ω^k) := by
  have hmul : ω^k*(1-ω^(5-k)) = ω^k-1 := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hk, hω.pow_eq_one]
  have hn := congrArg Complex.normSq hmul
  rw [Complex.normSq_mul, primitive_power_normSq hω, one_mul] at hn
  exact hn.trans (normSq_sub_comm _ _)

theorem primitive_chord_product {ω : ℂ} (hω : IsPrimitiveRoot ω 5) :
    Complex.normSq (1-ω)*Complex.normSq (1-ω^2) = 5 := by
  have hgeom : 1+ω+ω^2+ω^3+ω^4 = 0 := by
    have h := hω.geom_sum_eq_zero (by decide : 1 < 5)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  have hprod : (1-ω)*(1-ω^2)*(1-ω^3)*(1-ω^4) = 5 := by
    linear_combination (ω^6-2*ω^5+ω^3+3*ω-4)*hgeom
  have hn := congrArg Complex.normSq hprod
  simp only [Complex.normSq_mul] at hn
  rw [show Complex.normSq (1-ω^3) = Complex.normSq (1-ω^2) from
      primitive_distance_complement hω 2 (by decide),
    show Complex.normSq (1-ω^4) = Complex.normSq (1-ω) from
      by simpa using primitive_distance_complement hω 1 (by decide)] at hn
  norm_num at hn
  nlinarith [mul_nonneg (Complex.normSq_nonneg (1-ω))
    (Complex.normSq_nonneg (1-ω^2))]

theorem configuration_scale (u ω : ℂ) :
    pentagonConfiguration u ω = fun i => u * pentagonConfiguration 1 ω i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pentagonConfiguration]
  · simp [pentagonConfiguration]

theorem configuration_normSum {ω : ℂ} (hω : IsPrimitiveRoot ω 5) (u : ℂ) :
    normSum (pentagonConfiguration u ω) = 5 * Complex.normSq u := by
  unfold normSum pentagonConfiguration
  simp [Fin.sum_univ_succ, Complex.normSq_mul, primitive_power_normSq hω] <;> ring

theorem configuration_normSum_six {u ω : ℂ} (hu : Complex.normSq u = (6 : ℝ)/5)
    (hω : IsPrimitiveRoot ω 5) : normSum (pentagonConfiguration u ω) = 6 := by
  rw [configuration_normSum hω, hu]
  norm_num

theorem configuration_isCenteredPentagon {u ω : ℂ}
    (hu : Complex.normSq u = (6 : ℝ)/5) (hω : IsPrimitiveRoot ω 5) :
    IsCenteredPentagon (pentagonConfiguration u ω) := by
  refine ⟨u, ω, hu, hω, Equiv.refl _, ?_, ?_⟩
  · simp [pentagonConfiguration]
  · intro j
    simp [pentagonConfiguration]

end Pentagon
end N6

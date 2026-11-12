import N6.Statement
import Mathlib.Tactic

set_option autoImplicit false

namespace N6

theorem normSum_nonneg (z : Configuration) : 0 ≤ normSum z := by
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem pairs_explicit : pairs =
    {(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
      (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)} := by decide

noncomputable def center (z : Configuration) : Configuration :=
  fun i => z i - (∑ j, z j) / 6

theorem normSum_expand (z : Configuration) :
    normSum z = Complex.normSq (z 0) + Complex.normSq (z 1) +
      Complex.normSq (z 2) + Complex.normSq (z 3) + Complex.normSq (z 4) +
      Complex.normSq (z 5) := by
  simp [normSum, Fin.sum_univ_succ]
  ring

theorem sum_expand (z : Configuration) :
    (∑ i, z i) = z 0 + z 1 + z 2 + z 3 + z 4 + z 5 := by
  simp [Fin.sum_univ_succ]
  ring

theorem center_sum (z : Configuration) : ∑ i, center z i = 0 := by
  simp only [center, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem normSum_center (z : Configuration) :
    normSum (center z) = normSum z - Complex.normSq (∑ i, z i) / 6 := by
  rw [normSum_expand, normSum_expand, sum_expand]
  simp [center, sum_expand, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem discriminant_translate (z : Configuration) (c : ℂ) :
    discriminant (fun i => z i - c) = discriminant z := by
  unfold discriminant
  congr 1
  ext p
  congr 1
  ring

theorem normSum_scale (z : Configuration) (c : ℂ) :
    normSum (fun i => c * z i) = Complex.normSq c * normSum z := by
  simp only [normSum, Complex.normSq_mul, Finset.mul_sum]

theorem discriminant_scale (z : Configuration) (c : ℂ) :
    discriminant (fun i => c * z i) = Complex.normSq c ^ 15 * discriminant z := by
  simp only [discriminant, ← mul_sub, Complex.normSq_mul, Finset.prod_mul_distrib]
  rw [Finset.prod_const, pairs_card]

end N6

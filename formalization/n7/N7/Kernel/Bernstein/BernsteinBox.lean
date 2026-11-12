-- Adapted from the checked Eight.BernsteinBox general semantics.
import N7.Kernel.Bernstein.BernsteinCertificate
import N7.Kernel.Bernstein.ClosedCover

namespace N7.Kernel
open Checks

theorem unit_coordinate_between (lo hi : ℚ) {x : ℝ} (hw : lo < hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) :
    0 ≤ (x-lo)/(hi-lo : ℚ) ∧ (x-lo)/(hi-lo : ℚ) ≤ 1 := by
  have hp : (0 : ℝ) < (hi-lo : ℚ) := by exact_mod_cast sub_pos.mpr hw
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) hp.le
  · apply (div_le_one hp).mpr
    push_cast
    linarith [hx.2]

theorem affine_unit_coordinate (lo hi : ℚ) (x : ℝ) (hw : lo < hi) :
    (hi-lo : ℚ)*((x-lo)/(hi-lo : ℚ))+(lo : ℝ) = x := by
  have hp : (0 : ℝ) < (hi-lo : ℚ) := by exact_mod_cast sub_pos.mpr hw
  field_simp [ne_of_gt hp]
  ring

theorem DenseKernel.checked_affine_box_nonneg (p U V T : DenseKernel) (b : ClosedBox 3)
    (hw : ∀ i, b.lo i < b.hi i)
    (hU : denseCheck ((p.shiftU (b.lo 0)).rescaleU (b.hi 0-b.lo 0)) U = true)
    (hV : denseCheck ((U.shiftV (b.lo 1)).rescaleV (b.hi 1-b.lo 1)) V = true)
    (hT : denseCheck ((V.shiftT (b.lo 2)).rescaleT (b.hi 2-b.lo 2)) T = true)
    (hn : ∀ u v t : ℝ, (0 ≤ u ∧ u ≤ 1) → (0 ≤ v ∧ v ≤ 1) → (0 ≤ t ∧ t ≤ 1) → 0 ≤ T.real u v t)
    (x : Fin 3 → ℝ) (hx : b.Contains x) : 0 ≤ p.real (x 0) (x 1) (x 2) := by
  let u : ℝ := (x 0-b.lo 0)/(b.hi 0-b.lo 0 : ℚ)
  let v : ℝ := (x 1-b.lo 1)/(b.hi 1-b.lo 1 : ℚ)
  let t : ℝ := (x 2-b.lo 2)/(b.hi 2-b.lo 2 : ℚ)
  have h := hn u v t (unit_coordinate_between _ _ (hw 0) (hx 0))
    (unit_coordinate_between _ _ (hw 1) (hx 1)) (unit_coordinate_between _ _ (hw 2) (hx 2))
  rw [DenseKernel.affine_checked_real p U V T _ _ _ _ _ _ hU hV hT] at h
  dsimp [u,v,t] at h
  rw [affine_unit_coordinate _ _ _ (hw 0),affine_unit_coordinate _ _ _ (hw 1),
    affine_unit_coordinate _ _ _ (hw 2)] at h
  exact h

/-- Compose affine and Bernstein certificates into a theorem about every point of a closed box. -/
theorem DenseKernel.checked_box_nonneg (p U V T BU BV BT : DenseKernel) (b : ClosedBox 3)
    (hw : ∀ i, b.lo i < b.hi i)
    (hU : denseCheck ((p.shiftU (b.lo 0)).rescaleU (b.hi 0-b.lo 0)) U = true)
    (hV : denseCheck ((U.shiftV (b.lo 1)).rescaleV (b.hi 1-b.lo 1)) V = true)
    (hT : denseCheck ((V.shiftT (b.lo 2)).rescaleT (b.hi 2-b.lo 2)) T = true)
    (hBU : denseCheck T.bernU BU = true) (hBV : denseCheck BU.bernV BV = true)
    (hBT : denseCheck BV.bernT BT = true) (hpos : BT.nonnegCheck = true)
    (x : Fin 3 → ℝ) (hx : b.Contains x) : 0 ≤ p.real (x 0) (x 1) (x 2) := by
  let u : ℝ := (x 0-b.lo 0)/(b.hi 0-b.lo 0 : ℚ)
  let v : ℝ := (x 1-b.lo 1)/(b.hi 1-b.lo 1 : ℚ)
  let t : ℝ := (x 2-b.lo 2)/(b.hi 2-b.lo 2 : ℚ)
  have h := DenseKernel.bernstein_checked_nonneg T BU BV BT hBU hBV hBT hpos u v t
    (unit_coordinate_between _ _ (hw 0) (hx 0))
    (unit_coordinate_between _ _ (hw 1) (hx 1))
    (unit_coordinate_between _ _ (hw 2) (hx 2))
  rw [DenseKernel.affine_checked_real p U V T _ _ _ _ _ _ hU hV hT] at h
  dsimp [u,v,t] at h
  rw [affine_unit_coordinate _ _ _ (hw 0),affine_unit_coordinate _ _ _ (hw 1),
    affine_unit_coordinate _ _ _ (hw 2)] at h
  exact h

end N7.Kernel

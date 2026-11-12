import Eight.BernsteinBox
import Eight.BernsteinControl

namespace MordellEight
open Set
set_option maxHeartbeats 0

namespace ClosedBox
def Widths {n : ℕ} (b : ClosedBox n) : Prop := ∀ i,b.lo i<b.hi i
def midpoint {n : ℕ} (b : ClosedBox n) (axis : Fin n) : ℚ := (b.lo axis+b.hi axis)/2
def half {n : ℕ} (b : ClosedBox n) (axis : Fin n) (right : Bool) : ClosedBox n :=
  if right then b.right axis (b.midpoint axis) else b.left axis (b.midpoint axis)
noncomputable def coord {n : ℕ} (b : ClosedBox n) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (x i-b.lo i)/(b.hi i-b.lo i:ℚ)

theorem coord_unit {n : ℕ} {b : ClosedBox n} (hw : b.Widths) {x : Fin n → ℝ}
    (hx : b.Contains x) (i : Fin n) : 0≤b.coord x i ∧ b.coord x i≤1 :=
  unit_coordinate_between _ _ (hw i) (hx i)

theorem half_widths {n : ℕ} {b : ClosedBox n} (hw : b.Widths) (axis : Fin n) (right : Bool) :
    (b.half axis right).Widths := by
  intro i
  by_cases hi : i=axis
  · subst i
    cases right <;> simp [half,left,right,midpoint]
    all_goals linarith [hw axis]
  · cases right <;> simpa [half,left,right,Function.update_of_ne hi] using hw i

theorem half_subset {n : ℕ} {b : ClosedBox n} (hw : b.Widths) (axis : Fin n) (right : Bool)
    {x : Fin n → ℝ} (hx : (b.half axis right).Contains x) : b.Contains x := by
  intro i
  by_cases hi : i=axis
  · subst i
    have hl : (b.lo axis:ℝ)<b.hi axis := by exact_mod_cast hw axis
    have h := hx axis
    cases right <;> simp [half,left,right,midpoint] at h
    all_goals constructor <;> linarith [h.1,h.2]
  · have h := hx i
    cases right <;> simpa [half,left,right,Function.update_of_ne hi] using h

theorem half_cover {n : ℕ} (b : ClosedBox n) (axis : Fin n) {x : Fin n → ℝ} (hx : b.Contains x) :
    (b.half axis false).Contains x ∨ (b.half axis true).Contains x :=
  b.split_contains axis (b.midpoint axis) hx

theorem coord_half_same {n : ℕ} {b : ClosedBox n} (hw : b.Widths) (axis : Fin n)
    (right : Bool) (x : Fin n → ℝ) :
    b.coord x axis=RationalCube.halfCoordinate right ((b.half axis right).coord x axis) := by
  have hl : (b.lo axis:ℝ)<b.hi axis := by exact_mod_cast hw axis
  have hd : (b.hi axis:ℝ)-(b.lo axis:ℝ)≠0 := sub_ne_zero.mpr (ne_of_gt hl)
  have hd1 : ((b.lo axis:ℝ)+b.hi axis)/2-b.lo axis≠0 := by linarith
  have hd2 : (b.hi axis:ℝ)-((b.lo axis:ℝ)+b.hi axis)/2≠0 := by linarith
  have hd3 : -(b.lo axis:ℝ)+(b.hi axis:ℝ)≠0 := by linarith
  cases right <;> simp [coord,half,left,right,midpoint,RationalCube.halfCoordinate]
  all_goals field_simp [hd,hd1,hd2] <;> ring_nf
  all_goals field_simp [hd3] <;> ring

theorem coord_half_other {n : ℕ} (b : ClosedBox n) (axis i : Fin n) (hi : i≠axis)
    (right : Bool) (x : Fin n → ℝ) : (b.half axis right).coord x i=b.coord x i := by
  cases right <;> simp [coord,half,left,right,Function.update_of_ne hi]
end ClosedBox

namespace RationalCube
def splitAxis (p : RationalCube) (axis : Fin 3) (right : Bool) : RationalCube :=
  match axis with | 0 => p.splitU right | 1 => p.splitV right | 2 => p.splitT right
noncomputable def boxEval (p : RationalCube) (b : ClosedBox 3) (x : Fin 3 → ℝ) : ℝ :=
  p.bernEval 12 12 6 (b.coord x 0) (b.coord x 1) (b.coord x 2)

theorem splitAxis_boxEval (p : RationalCube) (hp : p.Shape 12 12 6) (b : ClosedBox 3)
    (hw : b.Widths) (axis : Fin 3) (right : Bool) (x : Fin 3 → ℝ) :
    (p.splitAxis axis right).boxEval (b.half axis right) x=p.boxEval b x := by
  fin_cases axis
  · change (p.splitU right).bernEval 12 12 6 ((b.half 0 right).coord x 0)
      ((b.half 0 right).coord x 1) ((b.half 0 right).coord x 2)=
      p.bernEval 12 12 6 (b.coord x 0) (b.coord x 1) (b.coord x 2)
    rw [splitU_eval p _ _ _ hp]
    congr 1
    · exact (ClosedBox.coord_half_same hw 0 right x).symm
    · exact ClosedBox.coord_half_other b 0 1 (by decide) right x
    · exact ClosedBox.coord_half_other b 0 2 (by decide) right x
  · change (p.splitV right).bernEval 12 12 6 ((b.half 1 right).coord x 0)
      ((b.half 1 right).coord x 1) ((b.half 1 right).coord x 2)=
      p.bernEval 12 12 6 (b.coord x 0) (b.coord x 1) (b.coord x 2)
    rw [splitV_eval p _ _ _ hp]
    congr 1
    · exact ClosedBox.coord_half_other b 1 0 (by decide) right x
    · exact (ClosedBox.coord_half_same hw 1 right x).symm
    · exact ClosedBox.coord_half_other b 1 2 (by decide) right x
  · change (p.splitT right).bernEval 12 12 6 ((b.half 2 right).coord x 0)
      ((b.half 2 right).coord x 1) ((b.half 2 right).coord x 2)=
      p.bernEval 12 12 6 (b.coord x 0) (b.coord x 1) (b.coord x 2)
    rw [splitT_eval p _ _ _ hp]
    congr 1
    · exact ClosedBox.coord_half_other b 2 0 (by decide) right x
    · exact ClosedBox.coord_half_other b 2 1 (by decide) right x
    · exact (ClosedBox.coord_half_same hw 2 right x).symm

theorem rounded_split_boxEval_le (p : RationalCube) (hp : p.Shape 12 12 6) (b : ClosedBox 3)
    (hw : b.Widths) (axis : Fin 3) (right : Bool) (bits : ℕ) {x : Fin 3 → ℝ}
    (hx : (b.half axis right).Contains x) :
    ((p.splitAxis axis right).roundControls bits).boxEval (b.half axis right) x≤p.boxEval b x := by
  have hw' := ClosedBox.half_widths hw axis right
  have h := roundControls_le bits (p.splitAxis axis right) 12 12 6 _ _ _
    (ClosedBox.coord_unit hw' hx 0) (ClosedBox.coord_unit hw' hx 1) (ClosedBox.coord_unit hw' hx 2)
  exact h.trans_eq (splitAxis_boxEval p hp b hw axis right x)
end RationalCube
end MordellEight

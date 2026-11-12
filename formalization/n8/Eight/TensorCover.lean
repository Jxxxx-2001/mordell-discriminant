import Eight.TangentTensor
import Eight.LocalLeaf
import Eight.OutsideLeaf
import Eight.RootTensor.Semantic

namespace MordellEight
open Checks RationalCube
set_option maxHeartbeats 0

/-- No frontier or unchecked leaf constructor exists in an accepted certificate. -/
inductive TensorCover where
  | outside : TensorCover
  | contact (tag : Fin 5) : TensorCover
  | positive (a logLower logUpper : ℚ) (terms : ℕ) : TensorCover
  | split (axis : Fin 3) (left right : TensorCover) : TensorCover

def TensorCover.check (bits : ℕ) (b : ClosedBox 3) (p : RationalCube) : TensorCover → Bool
  | .outside => outsideCheck b
  | .contact tag => localLeafCheck b tag
  | .positive a lo hi terms => logCheck a lo hi terms && tangentTensorCheck b p a hi
  | .split axis left right => p.shapeCheck 12 12 6 &&
      left.check bits (b.half axis false) ((p.splitAxis axis false).roundControls bits) &&
      right.check bits (b.half axis true) ((p.splitAxis axis true).roundControls bits)

def TensorMinorant (b : ClosedBox 3) (p : RationalCube) : Prop :=
  ∀ x,b.Contains x → p.boxEval b x≤exactMajorant.real (x 0) (x 1) (x 2)

theorem TensorMinorant.split {b : ClosedBox 3} {p : RationalCube}
    (hm : TensorMinorant b p) (hw : b.Widths) (hp : p.Shape 12 12 6)
    (axis : Fin 3) (right : Bool) (bits : ℕ) :
    TensorMinorant (b.half axis right) ((p.splitAxis axis right).roundControls bits) := by
  intro x hx
  exact (rounded_split_boxEval_le p hp b hw axis right bits hx).trans
    (hm x (ClosedBox.half_subset hw axis right hx))

/-- The recursion proves every real point in the entire closed root box, including cut planes. -/
theorem TensorCover.check_sound (tree : TensorCover) (bits : ℕ) :
    ∀ b p,b.Widths → TensorMinorant b p → tree.check bits b p=true →
      ∀ x,b.Contains x → CanonicalDomain x →
        Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2) := by
  induction tree with
  | outside =>
    intro b p hw hm hc x hx hd
    exact (outsideCheck_sound b hc hx hd.1 hd.2).elim
  | contact tag =>
    intro b p hw hm hc x hx hd
    exact localLeafCheck_sound b tag hc hx hd.1
  | positive a lo hi terms =>
    intro b p hw hm hc x hx hd
    have hh : logCheck a lo hi terms=true ∧ tangentTensorCheck b p a hi=true := by
      simpa only [TensorCover.check,Bool.and_eq_true] using hc
    have haQ : (0:ℚ)<a := (of_decide_eq_true hh.1).1
    have ha : (0:ℝ)<(a:ℝ) := by exact_mod_cast haQ
    have hlog := (logCheck_sound a lo hi terms hh.1).2
    have hdist : 0<x 0+x 1-2*x 2 := lt_of_lt_of_le (by norm_num) hd.1.2.2.2.2.2
    exact (tangentTensorCheck_sound b p a hi hh.2 hw ha hlog hx hdist).trans (hm x hx)
  | split axis left right ihl ihr =>
    intro b p hw hm hc x hx hd
    have hh : (p.shapeCheck 12 12 6=true ∧
        left.check bits (b.half axis false) ((p.splitAxis axis false).roundControls bits)=true) ∧
        right.check bits (b.half axis true) ((p.splitAxis axis true).roundControls bits)=true := by
      simpa only [TensorCover.check,Bool.and_eq_true] using hc
    have hp := shapeCheck_sound p 12 12 6 hh.1.1
    rcases b.half_cover axis hx with hl|hr
    · exact ihl _ _ (ClosedBox.half_widths hw axis false) (hm.split hw hp axis false bits) hh.1.2 x hl hd
    · exact ihr _ _ (ClosedBox.half_widths hw axis true) (hm.split hw hp axis true bits) hh.2 x hr hd

/-- This theorem requires an actual successful complete-tree check; no such tree is assumed. -/
theorem domainMajorant_of_tensorCover (tree : TensorCover)
    (hc : tree.check 80 domainBox RootTensor.BT=true) : DomainMajorant := by
  have hroot : TensorMinorant domainBox RootTensor.BT := RootTensor.box_minorant
  have hall := tree.check_sound 80 domainBox RootTensor.BT RootTensor.box_widths hroot hc
  intro u v t hd
  rcases le_total u v with huv|hvu
  · have h := hall ![u,v,t] (pairDomain_in_box hd) ⟨hd,huv⟩
    change Real.log (u+v-2*t)≤exactMajorant.real u v t at h
    rwa [exact_majorant_eq_kernel] at h
  · have h := hall ![v,u,t] (pairDomain_in_box (pairDomain_swap hd)) ⟨pairDomain_swap hd,hvu⟩
    change Real.log (v+u-2*t)≤exactMajorant.real v u t at h
    rw [exact_majorant_eq_kernel,majorantFromMatrices_swap v u t] at h
    simpa only [add_comm v u] using h

end MordellEight

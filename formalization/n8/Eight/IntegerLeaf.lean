import Eight.IntegerBasis

namespace MordellEight.IntegerLeaf
open FixedTensor IntegerCube RationalCube
set_option maxHeartbeats 0

def gap (p : Cube) (A B C E G : Int) : Cube :=
  IntegerCube.add (IntegerCube.scale A p) (IntegerCube.add (IntegerCube.scale B (IntegerBasis.controls 0))
    (IntegerCube.add (IntegerCube.scale C (IntegerBasis.controls 1))
      (IntegerCube.add (IntegerCube.scale E (IntegerBasis.controls 2)) (IntegerCube.scale G (IntegerBasis.controls 3)))))

/-- Only five scalar rational equalities; no rational tensor arithmetic at a leaf. -/
def parameters (b : ClosedBox 3) (a l : ℚ) (d A B C E G : Int) : Bool :=
  decide ((0:ℚ)<d ∧ (A:ℚ)=d*a/2^80 ∧
    (B:ℚ)=d*(-a*(l-1)-b.lo 0-b.lo 1+2*b.lo 2) ∧
    (C:ℚ) = -d*(b.hi 0-b.lo 0) ∧
    (E:ℚ) = -d*(b.hi 1-b.lo 1) ∧
    (G:ℚ) = 2*d*(b.hi 2-b.lo 2))

theorem gap_value (p : Cube) (b : ClosedBox 3) (a l : ℚ) (d A B C E G : Int)
    (h : parameters b a l d A B C E G=true) (x : Fin 3 → ℝ) :
    (raw (gap p A B C E G)).boxEval b x =
      (d:ℝ)*(gapControls b (decode p) a l).boxEval b x := by
  have hs := of_decide_eq_true h
  change (0:ℚ)<d ∧ _ at hs
  have hA : (A:ℝ)=(d:ℝ)*(a:ℝ)/2^80 := by exact_mod_cast hs.2.1
  have hB : (B:ℝ)=(d:ℝ)*(-(a:ℝ)*((l:ℝ)-1)-(b.lo 0:ℝ)-(b.lo 1:ℝ)+2*(b.lo 2:ℝ)) := by
    exact_mod_cast hs.2.2.1
  have hC : (C:ℝ) = -(d:ℝ)*((b.hi 0:ℝ)-(b.lo 0:ℝ)) := by exact_mod_cast hs.2.2.2.1
  have hE : (E:ℝ) = -(d:ℝ)*((b.hi 1:ℝ)-(b.lo 1:ℝ)) := by exact_mod_cast hs.2.2.2.2.1
  have hG : (G:ℝ) = 2*(d:ℝ)*((b.hi 2:ℝ)-(b.lo 2:ℝ)) := by exact_mod_cast hs.2.2.2.2.2
  simp only [gap,raw_add,raw_scale]
  rw [IntegerBasis.one,IntegerBasis.u,IntegerBasis.v,IntegerBasis.t,raw_decode]
  unfold boxEval gapControls distanceControls
  simp only [(bernSound _ _ _ _ _ _).add,(bernSound _ _ _ _ _ _).scale,
    BernsteinBasis.One.value,BernsteinBasis.U.value,BernsteinBasis.V.value,BernsteinBasis.T.value]
  push_cast
  rw [hA,hB,hC,hE,hG]
  ring

theorem majorant {p : Cube} {b : ClosedBox 3} (hw : b.Widths)
    (hm : TensorMinorant b (decode p)) (a l : ℚ) (d A B C E G : Int)
    (hp : parameters b a l d A B C E G=true)
    (hc : nonneg (gap p A B C E G)=true)
    (ha : (0:ℝ)<(a:ℝ)) (hl : Real.log (a:ℝ)≤(l:ℝ)) : BoxMajorant b := by
  intro x hx hd
  have hn := bernEval_nonneg (raw (gap p A B C E G)) 12 12 6 (nonneg_sound _ hc) _ _ _
    (ClosedBox.coord_unit hw hx 0) (ClosedBox.coord_unit hw hx 1) (ClosedBox.coord_unit hw hx 2)
  change 0≤(raw (gap p A B C E G)).boxEval b x at hn
  rw [gap_value p b a l d A B C E G hp x] at hn
  have hposQ : (0:ℚ)<d := (of_decide_eq_true hp).1
  have hpos : (0:ℝ)<(d:ℝ) := by exact_mod_cast hposQ
  have hgap := (mul_nonneg_iff_of_pos_left hpos).mp hn
  rw [gapControls_value b (decode p) a l x hw] at hgap
  have hdist : 0<x 0+x 1-2*x 2 := lt_of_lt_of_le (by norm_num) hd.1.2.2.2.2.2
  have ht := log_le_tangent hdist ha hl
  have hquot : (x 0+x 1-2*x 2)/(a:ℝ)≤(decode p).boxEval b x-((l:ℝ)-1) :=
    (div_le_iff₀ ha).mpr (by nlinarith)
  exact (ht.trans (by linarith)).trans (hm x hx)

end MordellEight.IntegerLeaf

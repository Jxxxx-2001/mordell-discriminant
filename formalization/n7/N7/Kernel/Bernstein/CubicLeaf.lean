-- Adapted from checked Eight/CubicLeaf.lean; point-count independent.
import N7.Kernel.Bernstein.CubicBasis
import N7.Kernel.CubicLog
import N7.Kernel.Bernstein.LeafSoundness

namespace N7.Kernel.CubicLeaf
open FixedTensor IntegerCube RationalCube

structure Term where
  coeff : Int
  i : Fin 4
  j : Fin 4
  k : Fin 4
deriving DecidableEq

def sumControls : List Term → Cube
  | [] => []
  | t::ts => IntegerCube.add (IntegerCube.scale t.coeff (CubicBasis.controls t.i t.j t.k)) (sumControls ts)

noncomputable def value (u v w : ℝ) : List Term → ℝ
  | [] => 0
  | t::ts => t.coeff * (u^t.i.val * v^t.j.val * w^t.k.val) + value u v w ts

theorem sum_value (ts : List Term) (u v w : ℝ) :
    (raw (sumControls ts)).bernEval 12 12 6 u v w = value u v w ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [sumControls, raw_add, raw_scale, (bernSound 12 12 6 u v w).add,
      (bernSound 12 12 6 u v w).scale, CubicBasis.value, ih, value, Rat.cast_intCast]

def gap (p : Cube) (A : Int) (ts : List Term) : Cube :=
  IntegerCube.add (IntegerCube.scale A p) (sumControls ts)

noncomputable def dist (b : ClosedBox 3) (u v t : ℝ) : ℝ :=
  ((b.hi 0-b.lo 0 : ℚ)*u+b.lo 0) + ((b.hi 1-b.lo 1 : ℚ)*v+b.lo 1) -
  2*((b.hi 2-b.lo 2 : ℚ)*t+b.lo 2)

theorem dist_coords (b : ClosedBox 3) (hw : b.Widths) (x : Fin 3 → ℝ) :
    dist b (b.coord x 0) (b.coord x 1) (b.coord x 2) = x 0 + x 1 - 2*x 2 := by
  unfold dist ClosedBox.coord
  rw [affine_unit_coordinate _ _ _ (hw 0), affine_unit_coordinate _ _ _ (hw 1),
      affine_unit_coordinate _ _ _ (hw 2)]

noncomputable def upper (l y : ℝ) : ℝ := l + y - y^2/2 + y^3/3

noncomputable def gram (b : ClosedBox 3) (u v t : ℝ) : ℝ :=
  ((b.hi 0-b.lo 0 : ℚ)*u+b.lo 0) * ((b.hi 1-b.lo 1 : ℚ)*v+b.lo 1) -
    ((b.hi 2-b.lo 2 : ℚ)*t+b.lo 2)^2

theorem gram_coords (b : ClosedBox 3) (hw : b.Widths) (x : Fin 3 → ℝ) :
    gram b (b.coord x 0) (b.coord x 1) (b.coord x 2) = x 0*x 1-x 2^2 := by
  unfold gram ClosedBox.coord
  rw [affine_unit_coordinate _ _ _ (hw 0), affine_unit_coordinate _ _ _ (hw 1),
      affine_unit_coordinate _ _ _ (hw 2)]

end N7.Kernel.CubicLeaf

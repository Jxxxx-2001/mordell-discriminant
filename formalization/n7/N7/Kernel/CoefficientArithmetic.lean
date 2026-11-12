import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

set_option autoImplicit false
namespace N7.Kernel

/-- Exact coefficient space needed by the seven-point kernel. -/
structure KernelCoeff where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving DecidableEq, Repr

instance : Zero KernelCoeff := ⟨⟨0,0,0⟩⟩
instance : Add KernelCoeff := ⟨fun u v => ⟨u.a+v.a,u.b+v.b,u.c+v.c⟩⟩
instance : Neg KernelCoeff := ⟨fun u => ⟨-u.a,-u.b,-u.c⟩⟩

noncomputable def KernelCoeff.real (u : KernelCoeff) : ℝ :=
  (u.a:ℝ)+(u.b:ℝ)*Real.log 2+(u.c:ℝ)*Real.log 3

def KernelCoeff.scale (a : ℚ) (c : KernelCoeff) : KernelCoeff :=
  ⟨a*c.a,a*c.b,a*c.c⟩

theorem KernelCoeff.real_zero : KernelCoeff.real 0=0 := by
  change ((0:ℚ):ℝ)+((0:ℚ):ℝ)*Real.log 2+((0:ℚ):ℝ)*Real.log 3=0
  norm_num

theorem KernelCoeff.real_add (c d : KernelCoeff) : (c+d).real=c.real+d.real := by
  change ((c.a+d.a:ℚ):ℝ)+((c.b+d.b:ℚ):ℝ)*Real.log 2+
    ((c.c+d.c:ℚ):ℝ)*Real.log 3=_
  simp only [Rat.cast_add,KernelCoeff.real]
  ring

theorem KernelCoeff.real_neg (c : KernelCoeff) : (-c).real = -c.real := by
  change ((-c.a:ℚ):ℝ)+((-c.b:ℚ):ℝ)*Real.log 2+((-c.c:ℚ):ℝ)*Real.log 3=_
  simp only [Rat.cast_neg,KernelCoeff.real]
  ring

theorem KernelCoeff.real_scale (a : ℚ) (c : KernelCoeff) :
    (c.scale a).real=(a:ℝ)*c.real := by
  simp only [KernelCoeff.real,KernelCoeff.scale,Rat.cast_mul]
  ring

end N7.Kernel

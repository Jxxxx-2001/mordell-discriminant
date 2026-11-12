import N7.Kernel.CoefficientArithmetic
import N7.Kernel.Checks.Intervals
import N7.Kernel.Checks.LogBounds

set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel
open Checks

def bernLog2Interval : QInterval := ⟨1013035739299659071135698605846798551586536899366/1461501637330902918203684832716283019655932542976, 1013035739299659071135698605846798551586536899367/1461501637330902918203684832716283019655932542976⟩

theorem bern_log2_checked : logCheck 2 bernLog2Interval.lo bernLog2Interval.hi 100 = true := by
  decide +kernel

theorem bern_log2_sound : bernLog2Interval.Contains (Real.log 2) := by
  simpa [QInterval.Contains] using
    logCheck_sound 2 bernLog2Interval.lo bernLog2Interval.hi 100 bern_log2_checked

def bernLog3Interval : QInterval := ⟨1605623658680292875964422218442907053547872076505/1461501637330902918203684832716283019655932542976, 1605623658680292875964422218442907053547872076506/1461501637330902918203684832716283019655932542976⟩

theorem bern_log3_checked : logCheck 3 bernLog3Interval.lo bernLog3Interval.hi 100 = true := by
  decide +kernel

theorem bern_log3_sound : bernLog3Interval.Contains (Real.log 3) := by
  simpa [QInterval.Contains] using
    logCheck_sound 3 bernLog3Interval.lo bernLog3Interval.hi 100 bern_log3_checked

def KernelCoeff.bound (a : KernelCoeff) : QInterval :=
  ((⟨a.a,a.a⟩ : QInterval).add (bernLog2Interval.scale a.b)).add
    (bernLog3Interval.scale a.c)

theorem KernelCoeff.bound_sound (a : KernelCoeff) : a.bound.Contains a.real :=
  QInterval.add_sound
    (QInterval.add_sound ⟨le_rfl,le_rfl⟩ (QInterval.scale_sound _ bern_log2_sound))
    (QInterval.scale_sound _ bern_log3_sound)

#print axioms KernelCoeff.bound_sound
end N7.Kernel

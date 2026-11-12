import Eight.IntegerLeaf
namespace MordellEight.DyadicLogs
open Checks
set_option maxHeartbeats 0

theorem upper_rounded (a lo hi : ℚ) (hl : Real.log (a:ℝ)≤(lo:ℝ))
    (hc : decide (lo≤hi)=true) : Real.log (a:ℝ)≤(hi:ℝ) := by
  exact hl.trans (by exact_mod_cast (of_decide_eq_true hc : lo≤hi))

namespace Log0
def a : ℚ := (965267/1048576)
def lo : ℚ := (-2069589630247528611/25000000000000000000)
def sourceHi : ℚ := (-8278358520990114443/100000000000000000000)
def hi : ℚ := (-50039606800258617297927/604462909807314587353088)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log0

namespace Log1
def a : ℚ := (965267/2097152)
def lo : ℚ := (-38796538288492322693/50000000000000000000)
def sourceHi : ℚ := (-15518615315396929077/20000000000000000000)
def hi : ℚ := (-234510684243129618979777/302231454903657293676544)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log1

namespace Log2
def a : ℚ := (1/4)
def lo : ℚ := (-34657359027997265471/25000000000000000000)
def sourceHi : ℚ := (-138629436111989061883/100000000000000000000)
def hi : ℚ := (-837963523372001241317209/604462909807314587353088)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log2

namespace Log3
def a : ℚ := (8687403/16777216)
def lo : ℚ := (-16453693252836574983/25000000000000000000)
def sourceHi : ℚ := (-65814773011346299931/100000000000000000000)
def hi : ℚ := (-795651784054926015561419/1208925819614629174706176)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log3

namespace Log4
def a : ℚ := (4826335/4194304)
def lo : ℚ := (14035996610430861133/100000000000000000000)
def sourceHi : ℚ := (7017998305215430567/50000000000000000000)
def hi : ℚ := (169684787063732857521441/1208925819614629174706176)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log4

namespace Log5
def a : ℚ := (2895801/4194304)
def lo : ℚ := (-9261641441542051797/25000000000000000000)
def sourceHi : ℚ := (-37046565766168207187/100000000000000000000)
def hi : ℚ := (-111966374706930406269659/302231454903657293676544)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log5

namespace Log6
def a : ℚ := (22201141/16777216)
def lo : ℚ := (2801219084794673087/10000000000000000000)
def sourceHi : ℚ := (28012190847946730871/100000000000000000000)
def hi : ℚ := (338646607800554158291817/1208925819614629174706176)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log6

namespace Log7
def a : ℚ := (24131675/16777216)
def lo : ℚ := (36350351741851836709/100000000000000000000)
def sourceHi : ℚ := (3635035174185183671/10000000000000000000)
def hi : ℚ := (439448787727982949626647/1208925819614629174706176)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log7

namespace Log8
def a : ℚ := (4826335/16777216)
def lo : ℚ := (-124593439501558200751/100000000000000000000)
def sourceHi : ℚ := (-498373758006232803/400000000000000000)
def hi : ℚ := (-1506242259680269625125067/1208925819614629174706176)
theorem checked : logCheck a lo sourceHi 64=true := by decide +kernel
theorem rounded : decide (sourceHi≤hi)=true := by decide +kernel
theorem positive : (0:ℝ)<(a:ℝ) := by norm_num [a]
theorem upper : Real.log (a:ℝ)≤(hi:ℝ) :=
  upper_rounded a sourceHi hi (logCheck_sound a lo sourceHi 64 checked).2 rounded
end Log8

end MordellEight.DyadicLogs

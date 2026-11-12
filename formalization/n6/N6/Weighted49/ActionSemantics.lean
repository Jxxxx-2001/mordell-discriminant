import N6.Weighted49.ActionGround000
import N6.Weighted49.ActionGround001
import N6.Weighted49.ActionGround002
import N6.Weighted49.ActionGround003
import N6.Weighted49.ActionGround004
import N6.Weighted49.ActionGround005
import N6.Weighted49.ActionGround006
import N6.Weighted49.ActionGround007
import N6.Weighted49.ActionGround008
import N6.Weighted49.ActionGround009
import N6.Weighted49.ActionGround010
import N6.Weighted49.ActionGround011
import N6.Weighted49.ActionGround012
import N6.Weighted49.SemanticsHelpers
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA000_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA000Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA000Pairs WA000Checked
theorem WA000_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA000 = 0 := by
  simpa only [WA000, parentData] using hP 0
#print axioms WA000_vanish
theorem WA001_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA001Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA001Pairs WA001Checked
theorem WA001_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA001 = 0 := by
  simpa only [WA001, parentData] using hP 1
#print axioms WA001_vanish
theorem WA002_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA002Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA002Pairs WA002Checked
theorem WA002_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA002 = 0 := by
  simpa only [WA002, parentData] using hP 2
#print axioms WA002_vanish
theorem WA003_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA003Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA003Pairs WA003Checked
theorem WA003_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA003 = 0 := by
  simpa only [WA003, parentData] using hP 3
#print axioms WA003_vanish
theorem WA004_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA004Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA004Pairs WA004Checked
theorem WA004_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA004 = 0 := by
  simpa only [WA004, parentData] using hP 4
#print axioms WA004_vanish
theorem WA005_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA005Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA005Pairs WA005Checked
theorem WA005_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA005 = 0 := by
  simpa only [WA005, parentData] using hP 5
#print axioms WA005_vanish
theorem WA006_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA006Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA006Pairs WA006Checked
theorem WA006_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA006 = 0 := by
  simpa only [WA006, parentData] using hP 6
#print axioms WA006_vanish
theorem WA007_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA007Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA007Pairs WA007Checked
theorem WA007_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA007 = 0 := by
  simpa only [WA007, parentData] using hP 7
#print axioms WA007_vanish
theorem WA008_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA008Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA008Pairs WA008Checked
theorem WA008_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA008 = 0 := by
  simpa only [WA008, parentData] using hP 8
#print axioms WA008_vanish
theorem WA009_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA009Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA009Pairs WA009Checked
theorem WA009_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA009 = 0 := by
  simpa only [WA009, parentData] using hP 9
#print axioms WA009_vanish
theorem WA010_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA010Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA010Pairs WA010Checked
theorem WA010_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA010 = 0 := by
  simpa only [WA010, parentData] using hP 10
#print axioms WA010_vanish
theorem WA011_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA011Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA011Pairs WA011Checked
theorem WA011_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA011 = 0 := by
  simpa only [WA011, parentData] using hP 11
#print axioms WA011_vanish
theorem WA012_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA012Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA012Pairs WA012Checked
theorem WA012_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA012 = 0 := by
  simpa only [WA012, parentData] using hP 12
#print axioms WA012_vanish
theorem WA013_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA013Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA013Pairs WA013Checked
theorem WA013_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA013 = 0 := by
  simpa only [WA013, parentData] using hP 13
#print axioms WA013_vanish
theorem WA014_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA014Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA014Pairs WA014Checked
theorem WA014_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA014 = 0 := by
  simpa only [WA014, parentData] using hP 14
#print axioms WA014_vanish
theorem WA015_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA015Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA015Pairs WA015Checked
theorem WA015_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA015 = 0 := by
  simpa only [WA015, parentData] using hP 15
#print axioms WA015_vanish
theorem WA016_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA016Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA016Pairs WA016Checked
theorem WA016_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA016 = 0 := by
  simpa only [WA016, parentData] using hP 16
#print axioms WA016_vanish
theorem WA017_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA017Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA017Pairs WA017Checked
theorem WA017_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA017 = 0 := by
  simpa only [WA017, parentData] using hP 17
#print axioms WA017_vanish
theorem WA018_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA018Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA018Pairs WA018Checked
theorem WA018_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA018 = 0 := by
  simpa only [WA018, parentData] using hP 18
#print axioms WA018_vanish
theorem WA019_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA019Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA019Pairs WA019Checked
theorem WA019_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA019 = 0 := by
  simpa only [WA019, parentData] using hP 19
#print axioms WA019_vanish
theorem WA020_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA020Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA020Pairs WA020Checked
theorem WA020_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA020 = 0 := by
  simpa only [WA020, parentData] using hP 20
#print axioms WA020_vanish
theorem WA021_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA021Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA021Pairs WA021Checked
theorem WA021_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA021 = 0 := by
  simpa only [WA021, parentData] using hP 21
#print axioms WA021_vanish
theorem WA022_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA022Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA022Pairs WA022Checked
theorem WA022_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA022 = 0 := by
  simpa only [WA022, parentData] using hP 22
#print axioms WA022_vanish
theorem WA023_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA023Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA023Pairs WA023Checked
theorem WA023_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA023 = 0 := by
  simpa only [WA023, parentData] using hP 23
#print axioms WA023_vanish
theorem WA024_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA024Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA024Pairs WA024Checked
theorem WA024_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA024 = 0 := by
  simpa only [WA024, parentData] using hP 24
#print axioms WA024_vanish
theorem WA025_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA025Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA025Pairs WA025Checked
theorem WA025_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA025 = 0 := by
  simpa only [WA025, parentData] using hP 25
#print axioms WA025_vanish
theorem WA026_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA026Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA026Pairs WA026Checked
theorem WA026_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA026 = 0 := by
  simpa only [WA026, parentData] using hP 26
#print axioms WA026_vanish
theorem WA027_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA027Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA027Pairs WA027Checked
theorem WA027_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA027 = 0 := by
  simpa only [WA027, parentData] using hP 27
#print axioms WA027_vanish
theorem WA028_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA028Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA028Pairs WA028Checked
theorem WA028_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA028 = 0 := by
  simpa only [WA028, parentData] using hP 28
#print axioms WA028_vanish
theorem WA029_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA029Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA029Pairs WA029Checked
theorem WA029_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA029 = 0 := by
  simpa only [WA029, parentData] using hP 29
#print axioms WA029_vanish
theorem WA030_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA030Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA030Pairs WA030Checked
theorem WA030_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA030 = 0 := by
  simpa only [WA030, parentData] using hP 30
#print axioms WA030_vanish
theorem WA031_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA031Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA031Pairs WA031Checked
theorem WA031_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA031 = 0 := by
  simpa only [WA031, parentData] using hP 31
#print axioms WA031_vanish
theorem WA032_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA032Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA032Pairs WA032Checked
theorem WA032_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA032 = 0 := by
  simpa only [WA032, parentData] using hP 32
#print axioms WA032_vanish
theorem WA033_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA033Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA033Pairs WA033Checked
theorem WA033_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA033 = 0 := by
  simpa only [WA033, parentData] using hP 33
#print axioms WA033_vanish
theorem WA034_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA034Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA034Pairs WA034Checked
theorem WA034_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA034 = 0 := by
  simpa only [WA034, parentData] using hP 34
#print axioms WA034_vanish
theorem WA035_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA035Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA035Pairs WA035Checked
theorem WA035_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA035 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA035_payload x
  simp only [WA035Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA035_vanish
theorem WA036_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA036Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA036Pairs WA036Checked
theorem WA036_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA036 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA036_payload x
  simp only [WA036Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA036_vanish
theorem WA037_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA037Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA037Pairs WA037Checked
theorem WA037_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA037 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA037_payload x
  simp only [WA037Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA037_vanish
theorem WA038_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA038Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA038Pairs WA038Checked
theorem WA038_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA038 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA038_payload x
  simp only [WA038Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA038_vanish
theorem WA039_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA039Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA039Pairs WA039Checked
theorem WA039_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA039 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA039_payload x
  simp only [WA039Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA039_vanish
theorem WA040_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA040Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA040Pairs WA040Checked
theorem WA040_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA040 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA040_payload x
  simp only [WA040Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA040_vanish
theorem WA041_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA041Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA041Pairs WA041Checked
theorem WA041_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA041 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q007 : value x N6.Quartics21.Case007.gData = 0 := by simpa only [parentData] using hP 6
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA041_payload x
  simp only [WA041Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA041_vanish
theorem WA042_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA042Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA042Pairs WA042Checked
theorem WA042_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA042 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q008 : value x N6.Quartics21.Case008.gData = 0 := by simpa only [parentData] using hP 7
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA042_payload x
  simp only [WA042Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q008, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA042_vanish
theorem WA043_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA043Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA043Pairs WA043Checked
theorem WA043_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA043 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q009 : value x N6.Quartics21.Case009.gData = 0 := by simpa only [parentData] using hP 8
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA043_payload x
  simp only [WA043Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q009, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA043_vanish
theorem WA044_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA044Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA044Pairs WA044Checked
theorem WA044_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA044 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q010 : value x N6.Quartics21.Case010.gData = 0 := by simpa only [parentData] using hP 9
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA044_payload x
  simp only [WA044Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q010, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA044_vanish
theorem WA045_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA045Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA045Pairs WA045Checked
theorem WA045_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA045 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q007 : value x N6.Quartics21.Case007.gData = 0 := by simpa only [parentData] using hP 6
  have h_D1Q008 : value x N6.Quartics21.Case008.gData = 0 := by simpa only [parentData] using hP 7
  have h_D1Q009 : value x N6.Quartics21.Case009.gData = 0 := by simpa only [parentData] using hP 8
  have h_D1Q010 : value x N6.Quartics21.Case010.gData = 0 := by simpa only [parentData] using hP 9
  have h_D1Q011 : value x N6.Quartics21.Case011.gData = 0 := by simpa only [parentData] using hP 10
  have h_D1Q012 : value x N6.Quartics21.Case012.gData = 0 := by simpa only [parentData] using hP 11
  have h_D1Q013 : value x N6.Quartics21.Case013.gData = 0 := by simpa only [parentData] using hP 12
  have h_D1Q014 : value x N6.Quartics21.Case014.gData = 0 := by simpa only [parentData] using hP 13
  have h_D1Q015 : value x N6.Quartics21.Case015.gData = 0 := by simpa only [parentData] using hP 14
  have h_D1Q016 : value x N6.Quartics21.Case016.gData = 0 := by simpa only [parentData] using hP 15
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA045_payload x
  simp only [WA045Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, h_D1Q015, h_D1Q016, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA045_vanish
theorem WA046_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA046Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA046Pairs WA046Checked
theorem WA046_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA046 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q007 : value x N6.Quartics21.Case007.gData = 0 := by simpa only [parentData] using hP 6
  have h_D1Q008 : value x N6.Quartics21.Case008.gData = 0 := by simpa only [parentData] using hP 7
  have h_D1Q009 : value x N6.Quartics21.Case009.gData = 0 := by simpa only [parentData] using hP 8
  have h_D1Q010 : value x N6.Quartics21.Case010.gData = 0 := by simpa only [parentData] using hP 9
  have h_D1Q011 : value x N6.Quartics21.Case011.gData = 0 := by simpa only [parentData] using hP 10
  have h_D1Q012 : value x N6.Quartics21.Case012.gData = 0 := by simpa only [parentData] using hP 11
  have h_D1Q013 : value x N6.Quartics21.Case013.gData = 0 := by simpa only [parentData] using hP 12
  have h_D1Q014 : value x N6.Quartics21.Case014.gData = 0 := by simpa only [parentData] using hP 13
  have h_D1Q015 : value x N6.Quartics21.Case015.gData = 0 := by simpa only [parentData] using hP 14
  have h_D1Q016 : value x N6.Quartics21.Case016.gData = 0 := by simpa only [parentData] using hP 15
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA046_payload x
  simp only [WA046Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, h_D1Q015, h_D1Q016, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA046_vanish
theorem WA047_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA047Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA047Pairs WA047Checked
theorem WA047_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA047 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q007 : value x N6.Quartics21.Case007.gData = 0 := by simpa only [parentData] using hP 6
  have h_D1Q008 : value x N6.Quartics21.Case008.gData = 0 := by simpa only [parentData] using hP 7
  have h_D1Q009 : value x N6.Quartics21.Case009.gData = 0 := by simpa only [parentData] using hP 8
  have h_D1Q010 : value x N6.Quartics21.Case010.gData = 0 := by simpa only [parentData] using hP 9
  have h_D1Q011 : value x N6.Quartics21.Case011.gData = 0 := by simpa only [parentData] using hP 10
  have h_D1Q012 : value x N6.Quartics21.Case012.gData = 0 := by simpa only [parentData] using hP 11
  have h_D1Q013 : value x N6.Quartics21.Case013.gData = 0 := by simpa only [parentData] using hP 12
  have h_D1Q014 : value x N6.Quartics21.Case014.gData = 0 := by simpa only [parentData] using hP 13
  have h_D1Q015 : value x N6.Quartics21.Case015.gData = 0 := by simpa only [parentData] using hP 14
  have h_D1Q016 : value x N6.Quartics21.Case016.gData = 0 := by simpa only [parentData] using hP 15
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA047_payload x
  simp only [WA047Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, h_D1Q015, h_D1Q016, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA047_vanish
theorem WA048_payload {R : Type*} [CommRing R] (x : Fin 5 → R) : pairs (value x) WA048Pairs = 0 :=
  N6.SparseProductReduce.pairs_vanish x WA048Pairs WA048Checked
theorem WA048_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    value x WA048 = 0 := by
  have h_D1Q001 : value x N6.Quartics21.Case001.gData = 0 := by simpa only [parentData] using hP 0
  have h_D1Q002 : value x N6.Quartics21.Case002.gData = 0 := by simpa only [parentData] using hP 1
  have h_D1Q003 : value x N6.Quartics21.Case003.gData = 0 := by simpa only [parentData] using hP 2
  have h_D1Q004 : value x N6.Quartics21.Case004.gData = 0 := by simpa only [parentData] using hP 3
  have h_D1Q005 : value x N6.Quartics21.Case005.gData = 0 := by simpa only [parentData] using hP 4
  have h_D1Q006 : value x N6.Quartics21.Case006.gData = 0 := by simpa only [parentData] using hP 5
  have h_D1Q007 : value x N6.Quartics21.Case007.gData = 0 := by simpa only [parentData] using hP 6
  have h_D1Q008 : value x N6.Quartics21.Case008.gData = 0 := by simpa only [parentData] using hP 7
  have h_D1Q009 : value x N6.Quartics21.Case009.gData = 0 := by simpa only [parentData] using hP 8
  have h_D1Q010 : value x N6.Quartics21.Case010.gData = 0 := by simpa only [parentData] using hP 9
  have h_D1Q011 : value x N6.Quartics21.Case011.gData = 0 := by simpa only [parentData] using hP 10
  have h_D1Q012 : value x N6.Quartics21.Case012.gData = 0 := by simpa only [parentData] using hP 11
  have h_D1Q013 : value x N6.Quartics21.Case013.gData = 0 := by simpa only [parentData] using hP 12
  have h_D1Q014 : value x N6.Quartics21.Case014.gData = 0 := by simpa only [parentData] using hP 13
  have h_D1Q015 : value x N6.Quartics21.Case015.gData = 0 := by simpa only [parentData] using hP 14
  have h_D1Q016 : value x N6.Quartics21.Case016.gData = 0 := by simpa only [parentData] using hP 15
  have h_D1Q017 : value x N6.Quartics21.Case017.gData = 0 := by simpa only [parentData] using hP 16
  have h_D1Q018 : value x N6.Quartics21.Case018.gData = 0 := by simpa only [parentData] using hP 17
  have h_D1Q019 : value x N6.Quartics21.Case019.gData = 0 := by simpa only [parentData] using hP 18
  have h_D1Q020 : value x N6.Quartics21.Case020.gData = 0 := by simpa only [parentData] using hP 19
  have h_D1Q022 : value x N6.BQ14.P022 = 0 := by simpa only [parentData] using hP 21
  have h_D1Q023 : value x N6.BQ14.P023 = 0 := by simpa only [parentData] using hP 22
  have h_D1Q024 : value x N6.BQ14.P024 = 0 := by simpa only [parentData] using hP 23
  have h_D1Q025 : value x N6.BQ14.P025 = 0 := by simpa only [parentData] using hP 24
  have h_D1Q026 : value x N6.BQ14.P026 = 0 := by simpa only [parentData] using hP 25
  have h_D1Q027 : value x N6.BQ14.P027 = 0 := by simpa only [parentData] using hP 26
  have h_D1Q028 : value x N6.BQ14.P028 = 0 := by simpa only [parentData] using hP 27
  have h_D1Q029 : value x N6.BQ14.P029 = 0 := by simpa only [parentData] using hP 28
  have h_D1Q030 : value x N6.BQ14.P030 = 0 := by simpa only [parentData] using hP 29
  have h_D1Q031 : value x N6.BQ14.P031 = 0 := by simpa only [parentData] using hP 30
  have h_D1Q032 : value x N6.BQ14.P032 = 0 := by simpa only [parentData] using hP 31
  have h_D1Q033 : value x N6.BQ14.P033 = 0 := by simpa only [parentData] using hP 32
  have h_D1Q034 : value x N6.BQ14.P034 = 0 := by simpa only [parentData] using hP 33
  have h_D1Q035 : value x N6.BQ14.P035 = 0 := by simpa only [parentData] using hP 34
  have h := WA048_payload x
  simp only [WA048Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, h_D1Q015, h_D1Q016, h_D1Q017, h_D1Q018, h_D1Q019, h_D1Q020, h_D1Q022, h_D1Q023, h_D1Q024, h_D1Q025, h_D1Q026, h_D1Q027, h_D1Q028, h_D1Q029, h_D1Q030, h_D1Q031, h_D1Q032, h_D1Q033, h_D1Q034, h_D1Q035, mul_zero, add_zero, zero_add, value_scalar, Int.cast_one, one_mul] at h
  exact h
#print axioms WA048_vanish
theorem all_actions_vanish {R : Type*} [CommRing R] (x : Fin 5 → R)
    (hP : ∀ i : Fin 35, value x (parentData i) = 0) :
    ∀ i : Fin 49, value x (actionData i) = 0 := by
  intro i
  fin_cases i
  · exact WA000_vanish x hP
  · exact WA001_vanish x hP
  · exact WA002_vanish x hP
  · exact WA003_vanish x hP
  · exact WA004_vanish x hP
  · exact WA005_vanish x hP
  · exact WA006_vanish x hP
  · exact WA007_vanish x hP
  · exact WA008_vanish x hP
  · exact WA009_vanish x hP
  · exact WA010_vanish x hP
  · exact WA011_vanish x hP
  · exact WA012_vanish x hP
  · exact WA013_vanish x hP
  · exact WA014_vanish x hP
  · exact WA015_vanish x hP
  · exact WA016_vanish x hP
  · exact WA017_vanish x hP
  · exact WA018_vanish x hP
  · exact WA019_vanish x hP
  · exact WA020_vanish x hP
  · exact WA021_vanish x hP
  · exact WA022_vanish x hP
  · exact WA023_vanish x hP
  · exact WA024_vanish x hP
  · exact WA025_vanish x hP
  · exact WA026_vanish x hP
  · exact WA027_vanish x hP
  · exact WA028_vanish x hP
  · exact WA029_vanish x hP
  · exact WA030_vanish x hP
  · exact WA031_vanish x hP
  · exact WA032_vanish x hP
  · exact WA033_vanish x hP
  · exact WA034_vanish x hP
  · exact WA035_vanish x hP
  · exact WA036_vanish x hP
  · exact WA037_vanish x hP
  · exact WA038_vanish x hP
  · exact WA039_vanish x hP
  · exact WA040_vanish x hP
  · exact WA041_vanish x hP
  · exact WA042_vanish x hP
  · exact WA043_vanish x hP
  · exact WA044_vanish x hP
  · exact WA045_vanish x hP
  · exact WA046_vanish x hP
  · exact WA047_vanish x hP
  · exact WA048_vanish x hP
#print axioms all_actions_vanish
end N6.Weighted49

import N6.Quartics21.All
import N6.Weighted49.ParentLocalGround000
import N6.Weighted49.ParentLocalGround001
import N6.Weighted49.ParentLocalGround002
import N6.Weighted49.ParentLocalGround003
import N6.Weighted49.SemanticsHelpers
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem D1Q022_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P022 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q022Pairs D1Q022Checked
  simp only [D1Q022Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q022Clearing D1Q022Clearing_ne_zero _ h
#print axioms D1Q022_from_inputs
theorem D1Q023_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P023 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q023Pairs D1Q023Checked
  simp only [D1Q023Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q023Clearing D1Q023Clearing_ne_zero _ h
#print axioms D1Q023_from_inputs
theorem D1Q024_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P024 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q024Pairs D1Q024Checked
  simp only [D1Q024Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q024Clearing D1Q024Clearing_ne_zero _ h
#print axioms D1Q024_from_inputs
theorem D1Q025_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P025 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q025Pairs D1Q025Checked
  simp only [D1Q025Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q025Clearing D1Q025Clearing_ne_zero _ h
#print axioms D1Q025_from_inputs
theorem D1Q026_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P026 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q026Pairs D1Q026Checked
  simp only [D1Q026Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q026Clearing D1Q026Clearing_ne_zero _ h
#print axioms D1Q026_from_inputs
theorem D1Q027_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P027 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q027Pairs D1Q027Checked
  simp only [D1Q027Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q027Clearing D1Q027Clearing_ne_zero _ h
#print axioms D1Q027_from_inputs
theorem D1Q028_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P028 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q028Pairs D1Q028Checked
  simp only [D1Q028Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q028Clearing D1Q028Clearing_ne_zero _ h
#print axioms D1Q028_from_inputs
theorem D1Q029_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P029 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q029Pairs D1Q029Checked
  simp only [D1Q029Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q029Clearing D1Q029Clearing_ne_zero _ h
#print axioms D1Q029_from_inputs
theorem D1Q030_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P030 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q030Pairs D1Q030Checked
  simp only [D1Q030Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q030Clearing D1Q030Clearing_ne_zero _ h
#print axioms D1Q030_from_inputs
theorem D1Q031_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P031 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q031Pairs D1Q031Checked
  simp only [D1Q031Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q031Clearing D1Q031Clearing_ne_zero _ h
#print axioms D1Q031_from_inputs
theorem D1Q032_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P032 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q032Pairs D1Q032Checked
  simp only [D1Q032Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q032Clearing D1Q032Clearing_ne_zero _ h
#print axioms D1Q032_from_inputs
theorem D1Q033_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P033 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q033Pairs D1Q033Checked
  simp only [D1Q033Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q033Clearing D1Q033Clearing_ne_zero _ h
#print axioms D1Q033_from_inputs
theorem D1Q034_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P034 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q034Pairs D1Q034Checked
  simp only [D1Q034Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q034Clearing D1Q034Clearing_ne_zero _ h
#print axioms D1Q034_from_inputs
theorem D1Q035_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : value x N6.BQ14.P035 = 0 := by
  have h_D1Q001 := N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q002 := N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q003 := N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q004 := N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q005 := N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q006 := N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q007 := N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q008 := N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q009 := N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q010 := N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q011 := N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q012 := N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q013 := N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  have h_D1Q014 := N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  have h := N6.SparseProductReduce.pairs_vanish x D1Q035Pairs D1Q035Checked
  simp only [D1Q035Pairs, pairs, h_D1Q001, h_D1Q002, h_D1Q003, h_D1Q004, h_D1Q005, h_D1Q006, h_D1Q007, h_D1Q008, h_D1Q009, h_D1Q010, h_D1Q011, h_D1Q012, h_D1Q013, h_D1Q014, mul_zero, add_zero, zero_add, value_scalar] at h
  exact N6.Certificate.int_scaled_zero D1Q035Clearing D1Q035Clearing_ne_zero _ h
#print axioms D1Q035_from_inputs
theorem parents_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : ∀ i : Fin 35, value x (parentData i) = 0 := by
  intro i
  fin_cases i
  · simpa only [parentData] using N6.Quartics21.Case001.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case002.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case003.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case004.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case005.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case006.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case007.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case008.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case009.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case010.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case011.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case012.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case013.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case014.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case015.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case016.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case017.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case018.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case019.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case020.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using N6.Quartics21.Case021.generic_vanish x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q022_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q023_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q024_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q025_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q026_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q027_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q028_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q029_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q030_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q031_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q032_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q033_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q034_from_inputs x h0 h1 h2 h3 hs
  · simpa only [parentData] using D1Q035_from_inputs x h0 h1 h2 h3 hs
#print axioms parents_from_inputs
end N6.Weighted49

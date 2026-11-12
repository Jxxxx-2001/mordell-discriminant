import N6.Even.ValueGround
import N6.Even.ProgramSemantics
import N6.Even.RootBounds
import N6.Univariate.IntegerSoundness

set_option autoImplicit false
namespace N6.Even.ValueCover
open N6.IntegerCover N6.SparseCheck N6.BranchEval.Program
open N6.Even.ProgramData

theorem p_binding (c : ℝ) : eval p c = N6.Even.p6 (K := ℝ) c := by
  norm_num [eval, p, N6.Even.p6] <;> ring

theorem v_binding (c : ℝ) : eval v c = (vden : ℝ)*V (K := ℝ) c := by
  have h := nf_invariant (pointC (K := ℝ) c) input6NF input6_den_ne_zero
  change value (pointC (K := ℝ) c) input6Num = (input6NF.den : ℝ)*V (K := ℝ) c at h
  calc
    eval v c = value (pointC (K := ℝ) c) input6Num := by
      simp [eval, v, input6Num, input6NumPart0, value, monVal, pointC,
        pm0, pm1, pm2, pm3, pm4, pm5] <;> ring
    _ = (vden : ℝ)*V (K := ℝ) c := by simpa only [input6NF, vden] using h

theorem root_value_bound (c : ℝ) (hp : N6.Even.p6 (K := ℝ) c = 0) :
    -(6 : ℝ)^12 < V (K := ℝ) c ∧ V (K := ℝ) c < (6 : ℝ)^12 := by
  have hc := N6.Even.p6_real_root_bounds c hp
  have hmem : (⟨-10,10,1⟩ : Bounds).Mem c := by simpa [Bounds.Mem] using hc
  have hp' : eval p c = 0 := by rw [p_binding, hp]
  have h := tree.sound p v vden 2176782336 ⟨-10,10,1⟩ c (by decide) checked hmem hp'
  rw [v_binding] at h
  have hd : (0 : ℝ) < vden := by exact_mod_cast vden_pos
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  norm_num only [Nat.reducePow]
  constructor <;> nlinarith [h.1,h.2]

#print axioms root_value_bound
end N6.Even.ValueCover

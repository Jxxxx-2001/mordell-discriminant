import Eight.Checks.RationalMatrix
import Eight.Constants

namespace MordellEight
open Matrix Checks
set_option maxHeartbeats 0
set_option maxRecDepth 10000

-- Exact entry [6,0,0] in the frozen eight-point kernel; descending powers decoded explicitly.
noncomputable def q6Entry00 : ℝ :=
  -6576334255/15465909004 + (-4/49*alpha+15/98)*logConstants 0 +
  (-8/49*alpha^2+23/98)*logConstants 1 +
  (8/49*alpha^2+4/49*alpha+11/98)*logConstants 2

def q6Lower : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(153/100000), (77530/86259169), (-128629/46063903), (152611/74898099);
    (77530/86259169), (5481161/60640039), (-3712693/13447769), (16678989/82794112);
    (-128629/46063903), (-3712693/13447769), (36018144/41918699), (-57092261/91222447);
    (152611/74898099), (16678989/82794112), (-57092261/91222447), (18521508/40422457)]
def q6FactorU : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, (7753000000/13197652857), (-12862900000/7047777159), (15261100000/11459409147);
    0, 1, (-11736079976861643764430424009948037322373/3842741161349727992978362366858364325991), (85726239464638717355987567682472288037657/38468070775247275758286605836792379394944);
    0, 0, 1, (-18034753180819134510734756376271781466824258010423360281598983329934497498997964487/27317751537303407528446484173591299115601047382191708388368399890905756675754157440);
    0, 0, 0, 1]
def q6InverseU : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, (-7753000000/13197652857), (118993221983168243316227147781485100000/3842741161349727992978362366858364325991), (-1110786012188281762809985116642929398535003993590856417740825755800871007180625/512207841324438891158371578254836858417519638416094532281907497954482937670390452);
    0, 1, (11736079976861643764430424009948037322373/3842741161349727992978362366858364325991), (-135889212277322591457954317420393784846298141050942149030541814026811479363835309/640259801655548613947964472818546073021899548020118165352384372443103672087988065);
    0, 0, 1, (18034753180819134510734756376271781466824258010423360281598983329934497498997964487/27317751537303407528446484173591299115601047382191708388368399890905756675754157440);
    0, 0, 0, 1]
def q6Pivots : Fin 4 → ℚ := ![(153/100000), (6203405331167782393302113/69033746373686898929657487), (1593627903084213788786978418876334561887171992728265662060195/99783768325865982594570218881673476195287876212291867122961563), (8258783973466580248227652602540629897842361204588475859020218634954281581511279544603966302073133526453342003/3660082859983669140846050618817639911945054131472186128118104950536919912759312711716044777667558343291798066720)]

theorem q6_rational_certificate : factorCheck q6Lower q6FactorU q6InverseU q6Pivots = true := by
  decide +kernel
theorem q6Lower_posDef : (realMatrix q6Lower).PosDef :=
  factorCheck_sound _ _ _ _ q6_rational_certificate

noncomputable def Q6 : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = 0 ∧ j = 0 then q6Entry00 else (q6Lower i j : ℝ)


theorem q6Entry00_lower : (153/100000 : ℝ) ≤ q6Entry00 := by
  have ha := alpha_bounds
  norm_num [alphaLo,alphaHi] at ha
  have hslo : (6234898018/10000000000 : ℝ)^2 ≤ alpha^2 := by nlinarith
  have hshi : alpha^2 ≤ (6234898019/10000000000 : ℝ)^2 := by nlinarith
  let b0 : ℝ := -4/49*alpha+15/98
  let b1 : ℝ := -8/49*alpha^2+23/98
  let b2 : ℝ := 8/49*alpha^2+4/49*alpha+11/98
  have hb0 : 0 ≤ b0 ∧ b0 ≤ (1021641/10000000) := by dsimp [b0]; constructor <;> nlinarith
  have hb1 : ((17122619/100000000) : ℝ) ≤ b1 := by dsimp [b1]; nlinarith
  have hb2 : ((2266097/10000000) : ℝ) ≤ b2 := by dsimp [b2]; nlinarith
  have h0 : ((1021641/10000000) : ℝ)*(-283663/1000000) ≤ b0*logConstants 0 := by
    calc
      _ ≤ b0*(-283663/1000000) := mul_le_mul_of_nonpos_right hb0.2 (by norm_num)
      _ ≤ b0*logConstants 0 := mul_le_mul_of_nonneg_left log0_bounds.1 hb0.1
  have h1 : ((17122619/100000000) : ℝ)*(44703111/50000000) ≤ b1*logConstants 1 :=
    mul_le_mul hb1 log1_bounds.1 (by norm_num) (by linarith)
  have h2 : ((2266097/10000000) : ℝ)*(33387771/25000000) ≤ b2*logConstants 2 :=
    mul_le_mul hb2 log2_bounds.1 (by norm_num) (by linarith)
  change (153/100000 : ℝ) ≤ -6576334255/15465909004+b0*logConstants 0+
    b1*logConstants 1+b2*logConstants 2
  linarith

theorem Q6_eq : Q6 = realMatrix q6Lower +
    Matrix.diagonal (fun i : Fin 4 => if i=0 then q6Entry00-153/100000 else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Q6,realMatrix,q6Lower,Matrix.diagonal_apply]

/-- Unconditional positivity of the actual eight-point kernel matrix Q6. -/
theorem Q6_posDef : Q6.PosDef := by
  rw [Q6_eq]
  apply q6Lower_posDef.add_posSemidef
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  split_ifs
  · exact sub_nonneg.mpr q6Entry00_lower
  · exact le_rfl

end MordellEight

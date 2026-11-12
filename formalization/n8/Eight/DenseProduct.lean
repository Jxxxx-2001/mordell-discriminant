import Eight.KernelSemantic
import Eight.DenseKernel

namespace MordellEight
set_option maxHeartbeats 0

theorem horner_mul_eval {A : Type} (e : A → ℝ) (p : List A) (c x : ℝ) :
    horner (fun a => c*e a) p x=c*horner e p x := by
  induction p with
  | nil => simp [horner]
  | cons a p ih => simp only [horner,ih]; ring

def DenseKernel.constant (c : KernelCoeff) : DenseKernel := [[[c]]]
def DenseKernel.mulU (p : DenseKernel) : DenseKernel := []::p
def DenseKernel.mulV (p : DenseKernel) : DenseKernel := p.map (fun row => []::row)
def DenseKernel.mulT (p : DenseKernel) : DenseKernel := p.map (List.map (fun row => 0::row))

theorem DenseKernel.constant_real (c : KernelCoeff) (u v t : ℝ) :
    (DenseKernel.constant c).real u v t=c.real := by simp [constant,DenseKernel.real,horner]

theorem DenseKernel.mulU_real (p : DenseKernel) (u v t : ℝ) :
    p.mulU.real u v t=u*p.real u v t := by simp [mulU,DenseKernel.real,horner]

theorem DenseKernel.mulV_real (p : DenseKernel) (u v t : ℝ) :
    p.mulV.real u v t=v*p.real u v t := by
  unfold mulV DenseKernel.real
  rw [horner_map]
  simp only [horner,zero_add]
  rw [horner_mul_eval]

theorem DenseKernel.mulT_real (p : DenseKernel) (u v t : ℝ) :
    p.mulT.real u v t=t*p.real u v t := by
  unfold mulT DenseKernel.real
  rw [horner_map]
  simp_rw [horner_map]
  simp only [horner,KernelCoeff.real_zero,zero_add]
  simp_rw [horner_mul_eval]

def axisValue (a : Fin 3) (u v t : ℝ) : ℝ := ![u,v,t] a
def DenseKernel.mulAxis (a : Fin 3) (p : DenseKernel) : DenseKernel :=
  if a=0 then p.mulU else if a=1 then p.mulV else p.mulT

theorem DenseKernel.mulAxis_real (a : Fin 3) (p : DenseKernel) (u v t : ℝ) :
    (p.mulAxis a).real u v t=axisValue a u v t*p.real u v t := by
  fin_cases a <;> simp [mulAxis,axisValue,mulU_real,mulV_real,mulT_real,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_def]

def DenseKernel.timesPoly (a : Fin 3) (p : DenseKernel) : List ℚ → DenseKernel
  | [] => []
  | c::q => denseOps.add (denseOps.scale c p) ((p.timesPoly a q).mulAxis a)

theorem DenseKernel.timesPoly_real (a : Fin 3) (p : DenseKernel) (q : List ℚ) (u v t : ℝ) :
    (p.timesPoly a q).real u v t=p.real u v t*horner (fun c : ℚ => (c : ℝ)) q (axisValue a u v t) := by
  induction q with
  | nil => simp [timesPoly,DenseKernel.real,horner]
  | cons c q ih =>
    rw [timesPoly,(denseSound u v t).add,(denseSound u v t).scale,mulAxis_real,ih,horner]
    ring

def DenseKernel.angularTimes (p : DenseKernel) : ℕ → DenseKernel
  | 0 => p
  | 1 => p.mulT
  | k+2 => denseOps.add (denseOps.scale 2 (p.angularTimes (k+1)).mulT)
      (denseOps.scale (-1) (p.angularTimes k).mulV.mulU)

theorem DenseKernel.angularTimes_real (p : DenseKernel) (k : ℕ) (u v t : ℝ) :
    (p.angularTimes k).real u v t=harmonic k u v t*p.real u v t := by
  induction k using Nat.twoStepInduction with
  | zero => simp [angularTimes,harmonic]
  | one => simp [angularTimes,harmonic,mulT_real]
  | more k ih ih' =>
    rw [angularTimes,(denseSound u v t).add,(denseSound u v t).scale,(denseSound u v t).scale,
      mulT_real,mulU_real,mulV_real,ih,ih',harmonic]
    norm_num
    ring

def DenseKernel.diagonalRow (a : Fin 3) : List KernelCoeff → DenseKernel
  | [] => []
  | c::q => denseOps.add (DenseKernel.constant c) ((DenseKernel.diagonalRow a q).mulAxis a)
def DenseKernel.diagonalPlane (a : Fin 3) : List (List KernelCoeff) → DenseKernel
  | [] => []
  | c::q => denseOps.add (DenseKernel.diagonalRow a c) ((DenseKernel.diagonalPlane a q).mulAxis a)
def DenseKernel.diagonalAt (a : Fin 3) : DenseKernel → DenseKernel
  | [] => []
  | c::q => denseOps.add (DenseKernel.diagonalPlane a c) ((DenseKernel.diagonalAt a q).mulAxis a)

theorem DenseKernel.diagonalRow_real (a : Fin 3) (p : List KernelCoeff) (u v t : ℝ) :
    (DenseKernel.diagonalRow a p).real u v t=horner KernelCoeff.real p (axisValue a u v t) := by
  induction p with
  | nil => rfl
  | cons c q ih =>
    rw [diagonalRow,(denseSound u v t).add,constant_real,mulAxis_real,ih,horner]

theorem DenseKernel.diagonalPlane_real (a : Fin 3) (p : List (List KernelCoeff)) (u v t : ℝ) :
    (DenseKernel.diagonalPlane a p).real u v t=
      horner (fun q => horner KernelCoeff.real q (axisValue a u v t)) p (axisValue a u v t) := by
  induction p with
  | nil => rfl
  | cons c q ih =>
    rw [diagonalPlane,(denseSound u v t).add,diagonalRow_real,mulAxis_real,ih,horner]

theorem DenseKernel.diagonalAt_real (a : Fin 3) (p : DenseKernel) (u v t : ℝ) :
    (p.diagonalAt a).real u v t=p.real (axisValue a u v t) (axisValue a u v t) (axisValue a u v t) := by
  induction p with
  | nil => rfl
  | cons c q ih =>
    rw [diagonalAt,(denseSound u v t).add,diagonalPlane_real,mulAxis_real,ih]
    rfl

def denseSum (p : List DenseKernel) : DenseKernel := p.foldr denseOps.add []
theorem denseSum_real (p : List DenseKernel) (u v t : ℝ) :
    (denseSum p).real u v t=(p.map (fun q => q.real u v t)).sum := by
  induction p with
  | nil => rfl
  | cons c q ih =>
    rw [denseSum,List.foldr_cons,(denseSound u v t).add]
    change c.real u v t+(denseSum q).real u v t=_
    rw [ih]
    rfl

end MordellEight

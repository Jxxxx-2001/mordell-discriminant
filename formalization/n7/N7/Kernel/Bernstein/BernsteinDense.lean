-- Adapted from the checked Eight.BernsteinDense general semantics.
import N7.Kernel.Bernstein.BernsteinKernel

namespace N7.Kernel
open Checks
set_option maxHeartbeats 0

def QOps.rescale {A : Type} (o : QOps A) (r : ℚ) : List A → List A
  | [] => []
  | a::p => a::(o.rescale r p).map (o.scale r)

theorem horner_rescale {A : Type} {o : QOps A} {e : A → ℝ} (h : QSound o e)
    (r : ℚ) (p : List A) (x : ℝ) : horner e (o.rescale r p) x = horner e p ((r : ℝ)*x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [QOps.rescale,horner,horner_scale h,ih]
    ring

def DenseKernel.rescaleU (r : ℚ) (p : DenseKernel) : DenseKernel := coeffOps.lift.lift.rescale r p
def DenseKernel.rescaleV (r : ℚ) (p : DenseKernel) : DenseKernel := p.map (coeffOps.lift.rescale r)
def DenseKernel.rescaleT (r : ℚ) (p : DenseKernel) : DenseKernel := p.map (List.map (coeffOps.rescale r))

theorem DenseKernel.rescaleU_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.rescaleU r).real u v t = p.real ((r : ℝ)*u) v t :=
  horner_rescale ((coeffSound.lift t).lift v) r p u

theorem DenseKernel.rescaleV_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.rescaleV r).real u v t = p.real u ((r : ℝ)*v) t := by
  unfold rescaleV DenseKernel.real
  rw [horner_map]
  simp_rw [horner_rescale (coeffSound.lift t)]

theorem DenseKernel.rescaleT_real (p : DenseKernel) (r : ℚ) (u v t : ℝ) :
    (p.rescaleT r).real u v t = p.real u v ((r : ℝ)*t) := by
  unfold rescaleT DenseKernel.real
  rw [horner_map]
  simp_rw [horner_map,horner_rescale coeffSound]

def DenseKernel.bernU (p : DenseKernel) : DenseKernel := coeffOps.lift.lift.bernstein p
def DenseKernel.bernV (p : DenseKernel) : DenseKernel := p.map coeffOps.lift.bernstein
def DenseKernel.bernT (p : DenseKernel) : DenseKernel := p.map (List.map coeffOps.bernstein)

def DenseKernel.nonnegCheck (p : DenseKernel) : Bool :=
  p.all (fun q => q.all (fun s => s.all (fun c => decide (0 ≤ c.bound.lo))))

theorem DenseKernel.nonnegCheck_sound {p : DenseKernel} (h : p.nonnegCheck = true) :
    ∀ q ∈ p, ∀ s ∈ q, ∀ c ∈ s, 0 ≤ c.real := by
  intro q hq s hs c hc
  have h1 := List.all_eq_true.mp h q hq
  have h2 := List.all_eq_true.mp h1 s hs
  have h3 : 0 ≤ c.bound.lo := of_decide_eq_true (List.all_eq_true.mp h2 c hc)
  have h3' : (0 : ℝ) ≤ (c.bound.lo : ℝ) := by exact_mod_cast h3
  exact h3'.trans c.bound_sound.1

/-- A check of all transformed coefficient bounds proves the entire continuous unit cube. -/
theorem DenseKernel.bernstein_sound (p : DenseKernel) (u v t : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (h : p.bernU.bernV.bernT.nonnegCheck = true) : 0 ≤ p.real u v t := by
  have hpos := DenseKernel.nonnegCheck_sound h
  apply N7.Kernel.bernstein_sound ((coeffSound.lift t).lift v) p u hu
  intro q hq
  apply N7.Kernel.bernstein_sound (coeffSound.lift t) q v hv
  intro s hs
  apply N7.Kernel.bernstein_sound coeffSound s t ht
  intro c hc
  have hq' : coeffOps.lift.bernstein q ∈ p.bernU.bernV := List.mem_map_of_mem hq
  have hq'' : (coeffOps.lift.bernstein q).map coeffOps.bernstein ∈ p.bernU.bernV.bernT :=
    List.mem_map_of_mem hq'
  have hs' : coeffOps.bernstein s ∈ (coeffOps.lift.bernstein q).map coeffOps.bernstein :=
    List.mem_map_of_mem hs
  exact hpos _ hq'' _ hs' _ hc

end N7.Kernel

import Eight.BernsteinKernel

namespace MordellEight
set_option maxHeartbeats 0

abbrev RationalCube := List (List (List ℚ))
def rationalOps : QOps ℚ := ⟨0,(·+·),(·*·)⟩
theorem rationalSound : QSound rationalOps (fun q => (q : ℝ)) := by
  constructor
  · norm_num [rationalOps]
  · intro a b; simp [rationalOps]
  · intro a b; simp [rationalOps]

noncomputable def RationalCube.real (p : RationalCube) (u v t : ℝ) : ℝ :=
  horner (fun q => horner (fun s => horner (fun a : ℚ => (a : ℝ)) s t) q v) p u

def RationalCube.check : RationalCube → RationalCube → Bool :=
  listCheck (listCheck (listCheck (fun a b => decide (a=b))))

theorem RationalCube.check_sound {p q : RationalCube} (h : p.check q = true) : p=q := by
  apply listCheck_sound _ ?_ p q h
  intro a b hab
  apply listCheck_sound _ ?_ a b hab
  intro c d hcd
  exact listCheck_sound _ (fun _ _ h => of_decide_eq_true h) c d hcd

def RationalCube.bernU (p : RationalCube) : RationalCube := rationalOps.lift.lift.bernstein p
def RationalCube.bernV (p : RationalCube) : RationalCube := p.map rationalOps.lift.bernstein
def RationalCube.bernT (p : RationalCube) : RationalCube := p.map (List.map rationalOps.bernstein)
def RationalCube.nonnegCheck (p : RationalCube) : Bool :=
  p.all (fun q => q.all (fun s => s.all (fun a => decide (0 ≤ a))))

theorem RationalCube.nonnegCheck_sound {p : RationalCube} (h : p.nonnegCheck = true) :
    ∀ q ∈ p, ∀ s ∈ q, ∀ c ∈ s, (0 : ℝ) ≤ (c : ℝ) := by
  intro q hq s hs c hc
  have h1 := List.all_eq_true.mp h q hq
  have h2 := List.all_eq_true.mp h1 s hs
  have h3 : 0 ≤ c := of_decide_eq_true (List.all_eq_true.mp h2 c hc)
  exact_mod_cast h3

theorem RationalCube.bernstein_sound (p : RationalCube) (u v t : ℝ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1)
    (h : p.bernU.bernV.bernT.nonnegCheck = true) : 0 ≤ p.real u v t := by
  have hp := RationalCube.nonnegCheck_sound h
  apply MordellEight.bernstein_sound ((rationalSound.lift t).lift v) p u hu
  intro q hq
  apply MordellEight.bernstein_sound (rationalSound.lift t) q v hv
  intro s hs
  apply MordellEight.bernstein_sound rationalSound s t ht
  intro c hc
  have hq' : rationalOps.lift.bernstein q ∈ p.bernU.bernV := List.mem_map_of_mem hq
  have hq'' : (rationalOps.lift.bernstein q).map rationalOps.bernstein ∈ p.bernU.bernV.bernT :=
    List.mem_map_of_mem hq'
  have hs' : rationalOps.bernstein s ∈ (rationalOps.lift.bernstein q).map rationalOps.bernstein :=
    List.mem_map_of_mem hs
  exact hp _ hq'' _ hs' _ hc

theorem RationalCube.checked_nonneg (p U V T : RationalCube)
    (hU : p.bernU.check U = true) (hV : U.bernV.check V = true)
    (hT : V.bernT.check T = true) (hc : T.nonnegCheck = true)
    (u v t : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ p.real u v t := by
  apply RationalCube.bernstein_sound p u v t hu hv ht
  rw [RationalCube.check_sound hU,RationalCube.check_sound hV,RationalCube.check_sound hT]
  exact hc

end MordellEight

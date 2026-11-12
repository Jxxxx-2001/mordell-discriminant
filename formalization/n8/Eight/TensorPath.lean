import Eight.TensorCover

namespace MordellEight
set_option maxHeartbeats 0

structure TensorState where
  box : ClosedBox 3
  controls : RationalCube

def TensorState.Valid (s : TensorState) : Prop := s.box.Widths ∧ TensorMinorant s.box s.controls
def TensorState.step (s : TensorState) (edge : Fin 3 × Bool) : TensorState :=
  ⟨s.box.half edge.1 edge.2,(s.controls.splitAxis edge.1 edge.2).roundControls 80⟩
def TensorState.follow : TensorState → List (Fin 3 × Bool) → TensorState
  | s,[] => s
  | s,e::path => (s.step e).follow path
def TensorState.pathCheck : TensorState → List (Fin 3 × Bool) → Bool
  | _,[] => true
  | s,e::path => s.controls.shapeCheck 12 12 6 && (s.step e).pathCheck path

theorem TensorState.pathCheck_sound (path : List (Fin 3 × Bool)) :
    ∀ s : TensorState,s.Valid → s.pathCheck path=true → (s.follow path).Valid := by
  induction path with
  | nil => intro s hs hc; exact hs
  | cons e path ih =>
    intro s hs hc
    have hh : s.controls.shapeCheck 12 12 6=true ∧ (s.step e).pathCheck path=true := by
      simpa only [pathCheck,Bool.and_eq_true] using hc
    have hp := RationalCube.shapeCheck_sound _ _ _ _ hh.1
    apply ih (s.step e) ?_ hh.2
    exact ⟨ClosedBox.half_widths hs.1 e.1 e.2,hs.2.split hs.1 hp e.1 e.2 80⟩

def rootTensorState : TensorState := ⟨domainBox,RootTensor.BT⟩
theorem rootTensorState_valid : rootTensorState.Valid :=
  ⟨RootTensor.box_widths,RootTensor.box_minorant⟩

end MordellEight

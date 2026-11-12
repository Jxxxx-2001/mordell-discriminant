import Eight.TensorPath

namespace MordellEight

/-- A proved bound on the whole closed box, restricted to the actual pair domain. -/
def BoxMajorant (b : ClosedBox 3) : Prop :=
  ∀ x,b.Contains x → CanonicalDomain x →
    Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2)

/-- Independently checked chunks can be joined without recomputing their tensors. -/
theorem BoxMajorant.join {b : ClosedBox 3} (axis : Fin 3)
    (hl : BoxMajorant (b.half axis false))
    (hr : BoxMajorant (b.half axis true)) : BoxMajorant b := by
  intro x hx hd
  rcases b.half_cover axis hx with h|h
  · exact hl x h hd
  · exact hr x h hd

theorem TensorState.majorant_of_check (s : TensorState) (hs : s.Valid)
    (tree : TensorCover) (hc : tree.check 80 s.box s.controls=true) : BoxMajorant s.box :=
  tree.check_sound 80 s.box s.controls hs.1 hs.2 hc

theorem domainMajorant_of_rootBox (h : BoxMajorant domainBox) : DomainMajorant := by
  intro u v t hd
  rcases le_total u v with huv|hvu
  · have hb := h ![u,v,t] (pairDomain_in_box hd) ⟨hd,huv⟩
    change Real.log (u+v-2*t)≤exactMajorant.real u v t at hb
    rwa [exact_majorant_eq_kernel] at hb
  · have hb := h ![v,u,t] (pairDomain_in_box (pairDomain_swap hd)) ⟨pairDomain_swap hd,hvu⟩
    change Real.log (v+u-2*t)≤exactMajorant.real v u t at hb
    rw [exact_majorant_eq_kernel,majorantFromMatrices_swap v u t] at hb
    simpa only [add_comm v u] using hb

end MordellEight

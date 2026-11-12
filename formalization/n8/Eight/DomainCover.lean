import Eight.ClosedCover
import Eight.KernelBridge
import Eight.UpperReduction

namespace MordellEight
set_option maxHeartbeats 0

def domainBox : ClosedBox 3 :=
  ⟨![0,0,-965267/524288],![965267/524288,965267/524288,965267/524288]⟩

theorem pairDomain_in_box {u v t : ℝ} (h : PairDomain u v t) :
    domainBox.Contains ![u,v,t] := by
  have hp : (0:ℝ)≤965267/524288 := by norm_num
  have hm := mul_le_mul h.2.2.1 h.2.2.2.1 h.2.1 hp
  have hl : -(965267/524288:ℝ)≤t := by nlinarith [h.2.2.2.2.1]
  have hu : t≤(965267/524288:ℝ) := by nlinarith [h.2.2.2.2.1]
  intro i
  fin_cases i <;> norm_num [domainBox,Matrix.cons_val_two]
  · exact ⟨h.1,h.2.2.1⟩
  · exact ⟨h.2.1,h.2.2.2.1⟩
  · exact ⟨hl,hu⟩

def CanonicalDomain (x : Fin 3 → ℝ) : Prop := PairDomain (x 0) (x 1) (x 2) ∧ x 0≤x 1

theorem pairDomain_swap {u v t : ℝ} (h : PairDomain u v t) : PairDomain v u t := by
  rcases h with ⟨hu,hv,huU,hvU,ht,hd⟩
  exact ⟨hv,hu,hvU,huU,by simpa [mul_comm] using ht,by simpa [add_comm] using hd⟩

/-- The certificate carries a proof for the same exact polynomial, including domain restriction. -/
structure LeafCertificate where
  box : ClosedBox 3
  bound : ∀ x,box.Contains x → CanonicalDomain x →
    Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2)

theorem domainMajorant_of_tree (tree : ClosedTree 3)
    (geometry : tree.check domainBox=true)
    (leaves : ∀ id box,(id,box)∈tree.leaves → ∀ x,box.Contains x → CanonicalDomain x →
      Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2)) : DomainMajorant := by
  have hc := tree.forall_of_check domainBox
    (fun x => CanonicalDomain x → Real.log (x 0+x 1-2*x 2)≤exactMajorant.real (x 0) (x 1) (x 2))
    geometry leaves
  intro u v t h
  rcases le_total u v with huv|hvu
  · have hb := hc ![u,v,t] (pairDomain_in_box h) ⟨h,huv⟩
    change Real.log (u+v-2*t)≤exactMajorant.real u v t at hb
    rwa [exact_majorant_eq_kernel] at hb
  · have hb := hc ![v,u,t] (pairDomain_in_box (pairDomain_swap h)) ⟨pairDomain_swap h,hvu⟩
    change Real.log (v+u-2*t)≤exactMajorant.real v u t at hb
    rw [exact_majorant_eq_kernel,majorantFromMatrices_swap v u t] at hb
    simpa only [add_comm v u] using hb

end MordellEight

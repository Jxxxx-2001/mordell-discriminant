import Chalk.Products

open Finset
namespace Chalk

private theorem witness (p : ℕ) (hp : 8 ≤ p) :
    ∃ z : Fin (p+2) → ℂ, energy z = (p:ℝ)+2 ∧
      ((p:ℝ)+2)^((p+2).choose 2) / ((p:ℝ)+1)^((p+1).choose 2) < delta z := by
  have hpos : 0<p := by omega
  let x : ℝ := p
  have hx : 0 ≤ x := Nat.cast_nonneg _
  let R := Real.sqrt (x+3)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2=x+3 := Real.sq_sqrt (by positivity)
  let ζ := Complex.exp (2*Real.pi*Complex.I/p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hpos.ne'
  obtain ⟨β,hβ⟩ := IsAlgClosed.exists_pow_nat_eq Complex.I hpos
  have hβn : ‖β‖=1 := (pow_left_inj₀ (norm_nonneg _) zero_le_one hpos.ne').mp (by
    rw [←norm_pow, hβ, Complex.norm_I, one_pow])
  let α : ℂ := β*(R:ℂ)
  have hα : α^p=Complex.I*(R:ℂ)^p := by simp [α,mul_pow,hβ]
  have hαn : ‖α‖=R := by simp [α,hβn,Real.norm_of_nonneg hR]
  let w := fun j : Fin p => ζ^j.val*α
  let W : Fin (p+2) → ℂ := Fin.cases 1 (Fin.cases (-1) w)
  have hw (j : Fin p) : ‖w j‖=R := by simp [w,hζ.norm'_eq_one hpos.ne',hαn]
  have hEW : energy W = 2+x*(x+3) := by
    simp [energy,W,Fin.sum_univ_succ,hw,hR2,x]; ring
  have hDw : delta w = (x+3)^(p.choose 2)*x^p := by
    simpa only [w, mul_comm α, hαn, hR2, unit_ring_delta hpos hζ] using
      delta_scale α (fun j : Fin p => ζ^j.val)
  have cross (a : ℝ) : (x+3)^p ≤ ∏ j, ‖(a:ℂ)-w j‖^2 := by
    rw [←hR2, ←cross_product hpos hζ R a hα]
    linarith [sq_nonneg (a^p)]
  have plus := cross 1
  have minus := cross (-1)
  push_cast at plus minus
  let N := (p+2).choose 2
  have hN : N = (p+1).choose 2 + (p+1) := by
    simp [N,Nat.choose_succ_succ,add_comm]
  have hprev : (p+1).choose 2 = p.choose 2+p := by
    rw [Nat.choose_succ_succ,Nat.choose_one_right,add_comm]
  have hW : 4*x^p*(x+3)^(N-1) ≤ delta W := by
    change _ ≤ delta (Fin.cases 1 (Fin.cases (-1) w))
    rw [delta_cons,Fin.prod_univ_succ,delta_cons,hDw]
    simp only [Fin.cases_zero,Fin.cases_succ,sub_neg_eq_add]
    norm_num only [one_add_one_eq_two,Complex.norm_ofNat, Nat.reducePow]
    have he : N-1=p.choose 2+p+p := by omega
    rw [he,pow_add,pow_add]
    calc
      _ = (4*(x+3)^p)*((x+3)^p*((x+3)^(p.choose 2)*x^p)) := by ring
      _ ≤ _ := by gcongr
  have hI := integer_bound (p+2) (by omega)
  rw [←Nat.choose_two_right, show p+2-1=p+1 by omega, Nat.add_sub_cancel] at hI
  have hbig : (x+1)^(p+1)*(x+2)^N < delta W := by
    apply lt_of_lt_of_le _ hW
    dsimp [x,N]
    exact_mod_cast hI
  let c : ℂ := ((Real.sqrt (x+1))⁻¹ : ℝ)
  have hc : ‖c‖^2 = (x+1)⁻¹ := by
    simp [c,inv_pow,Real.sq_sqrt (show 0 ≤ x+1 by positivity),Real.norm_eq_abs,sq_abs]
  refine ⟨fun i => c*W i, ?_, ?_⟩
  · rw [energy_scale,hc,hEW]
    change (x+1)⁻¹*(2+x*(x+3))=x+2
    field_simp; ring
  · rw [delta_scale,hc,inv_pow,inv_mul_eq_div]
    change (x+2)^N/(x+1)^((p+1).choose 2) < delta W/(x+1)^N
    apply (lt_div_iff₀ (by positivity)).mpr
    calc
      _ = (x+1)^(p+1)*(x+2)^N := by
        nth_rw 2 [hN]
        rw [pow_add]; field_simp
      _ < _ := hbig

/-- For every n ≥ 10 a normalized configuration strictly exceeds Chalk's ring value. -/
theorem exists_above_chalk (n : ℕ) (hn : 10 ≤ n) :
    ∃ z : Fin n → ℂ, (∑ i, ‖z i‖^2) = (n:ℝ) ∧
      (n:ℝ)^(n*(n-1)/2) / ((n-1:ℕ):ℝ)^((n-1)*(n-2)/2) <
        ∏ i, ∏ j, if i<j then ‖z i-z j‖^2 else 1 := by
  obtain ⟨p,rfl⟩ : ∃ p, n=p+2 := ⟨n-2, by omega⟩
  simpa [energy,delta,Nat.choose_two_right] using witness p (by omega)

end Chalk

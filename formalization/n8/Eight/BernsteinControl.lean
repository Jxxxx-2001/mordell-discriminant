import Eight.BernsteinTensor

namespace MordellEight
set_option maxHeartbeats 0

theorem homogeneous_mono {A : Type} (e f : A → ℝ) (n : ℕ) (p : List A)
    (h : ∀ a∈p,e a≤f a) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    homogeneous e n p x y≤homogeneous f n p x y := by
  induction p generalizing n with
  | nil => exact le_rfl
  | cons a p ih =>
    exact add_le_add (mul_le_mul_of_nonneg_right (h a (by simp)) (pow_nonneg hy _))
      (mul_le_mul_of_nonneg_left (ih (n-1) (fun b hb => h b (by simp [hb]))) hx)

namespace RationalCube
def ops : QOps RationalCube := rationalOps.lift.lift.lift
theorem bernSound (nu nv nt : ℕ) (u v t : ℝ) :
    QSound ops (fun p => p.bernEval nu nv nt u v t) :=
  ((rationalSound.homLift nt t (1-t)).homLift nv v (1-v)).homLift nu u (1-u)

def lowerControlCheck (p q : RationalCube) : Bool :=
  zipCheck (zipCheck (zipCheck (fun a b => decide (b≤a)))) p q
theorem lowerControlCheck_sound (p q : RationalCube) (hc : p.lowerControlCheck q=true)
    (nu nv nt : ℕ) (u v t : ℝ) (hu : 0≤u ∧ u≤1) (hv : 0≤v ∧ v≤1) (ht : 0≤t ∧ t≤1) :
    q.bernEval nu nv nt u v t≤p.bernEval nu nv nt u v t := by
  apply homogeneous_le _ _ _ ?_ nu p q hc u (1-u) hu.1 (by linarith)
  intro a b hab
  apply homogeneous_le _ _ _ ?_ nv a b hab v (1-v) hv.1 (by linarith)
  intro c d hcd
  apply homogeneous_le _ _ _ ?_ nt c d hcd t (1-t) ht.1 (by linarith)
  intro a b hab
  exact_mod_cast (of_decide_eq_true hab : b≤a)

def roundDownAt (bits : ℕ) (q : ℚ) : ℚ := (⌊q*(2^bits:ℚ)⌋:ℚ)/(2^bits:ℚ)
theorem roundDownAt_le (bits : ℕ) (q : ℚ) : roundDownAt bits q≤q := by
  unfold roundDownAt
  apply (div_le_iff₀ (pow_pos (by norm_num : (0:ℚ)<2) bits)).mpr
  exact Int.floor_le _
def roundControls (bits : ℕ) (p : RationalCube) : RationalCube :=
  p.map (List.map (List.map (roundDownAt bits)))

theorem roundControls_le (bits : ℕ) (p : RationalCube) (nu nv nt : ℕ) (u v t : ℝ)
    (hu : 0≤u ∧ u≤1) (hv : 0≤v ∧ v≤1) (ht : 0≤t ∧ t≤1) :
    (p.roundControls bits).bernEval nu nv nt u v t≤p.bernEval nu nv nt u v t := by
  unfold roundControls bernEval
  rw [homogeneous_map]
  apply homogeneous_mono _ _ _ _ ?_ _ _ hu.1 (by linarith)
  intro row hr
  rw [homogeneous_map]
  apply homogeneous_mono _ _ _ _ ?_ _ _ hv.1 (by linarith)
  intro col hc
  rw [homogeneous_map]
  apply homogeneous_mono _ _ _ _ ?_ _ _ ht.1 (by linarith)
  intro q hq
  exact_mod_cast roundDownAt_le bits q

theorem roundControls_shape (bits : ℕ) (p : RationalCube) (nu nv nt : ℕ) (hp : p.Shape nu nv nt) :
    (p.roundControls bits).Shape nu nv nt := by
  refine ⟨by simpa [roundControls] using hp.1,?_⟩
  intro row hr
  change row ∈ p.map (List.map (List.map (roundDownAt bits))) at hr
  obtain ⟨r,hrp,he⟩ := List.mem_map.mp hr
  subst row
  refine ⟨by simpa using (hp.2 r hrp).1,?_⟩
  intro col hc
  obtain ⟨c,hcr,hec⟩ := List.mem_map.mp hc
  subst col
  simpa using (hp.2 r hrp).2 c hcr

end RationalCube
end MordellEight

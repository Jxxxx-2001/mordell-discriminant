-- Adapted from the checked Eight.BernsteinTensor general semantics.
import N7.Kernel.Bernstein.BernsteinSubdivision
import N7.Kernel.Bernstein.RationalLower

namespace N7.Kernel
set_option maxHeartbeats 0

theorem homogeneous_map {A B : Type} (f : A → B) (e : B → ℝ)
    (n : ℕ) (p : List A) (x y : ℝ) :
    homogeneous e n (p.map f) x y=homogeneous (fun a => e (f a)) n p x y := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih => simp only [List.map_cons,homogeneous,ih]

theorem homogeneous_congr {A : Type} (e f : A → ℝ) (n : ℕ) (p : List A)
    (h : ∀ a∈p,e a=f a) (x y : ℝ) : homogeneous e n p x y=homogeneous f n p x y := by
  induction p generalizing n with
  | nil => rfl
  | cons a p ih =>
    simp only [homogeneous,h a (by simp),ih (n-1) (fun b hb => h b (by simp [hb]))]

namespace RationalCube

def Shape (p : RationalCube) (nu nv nt : ℕ) : Prop :=
  p.length=nu+1 ∧ ∀ row∈p,row.length=nv+1 ∧ ∀ col∈row,col.length=nt+1
def shapeCheck (p : RationalCube) (nu nv nt : ℕ) : Bool :=
  decide (p.length=nu+1) && p.all (fun row => decide (row.length=nv+1) &&
    row.all (fun col => decide (col.length=nt+1)))
theorem shapeCheck_sound (p : RationalCube) (nu nv nt : ℕ) (hc : p.shapeCheck nu nv nt=true) :
    p.Shape nu nv nt := by
  have h : decide (p.length=nu+1)=true ∧
      p.all (fun row => decide (row.length=nv+1) && row.all (fun col => decide (col.length=nt+1)))=true :=
    by simpa only [shapeCheck,Bool.and_eq_true] using hc
  refine ⟨of_decide_eq_true h.1,?_⟩
  intro row hr
  have hh : decide (row.length=nv+1)=true ∧ row.all (fun col => decide (col.length=nt+1))=true := by
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp h.2 row hr
  exact ⟨of_decide_eq_true hh.1,fun col hcol => of_decide_eq_true (List.all_eq_true.mp hh.2 col hcol)⟩

noncomputable def bernEval (p : RationalCube) (nu nv nt : ℕ) (u v t : ℝ) : ℝ :=
  homogeneous (fun row => homogeneous (fun col => homogeneous (fun q : ℚ => (q:ℝ)) nt col t (1-t))
    nv row v (1-v)) nu p u (1-u)

def splitU (p : RationalCube) (right : Bool) : RationalCube :=
  if right then rationalOps.lift.lift.bernRight p else rationalOps.lift.lift.bernLeft p
def splitV (p : RationalCube) (right : Bool) : RationalCube :=
  p.map (fun row => if right then rationalOps.lift.bernRight row else rationalOps.lift.bernLeft row)
def splitT (p : RationalCube) (right : Bool) : RationalCube :=
  p.map (List.map (fun col => if right then rationalOps.bernRight col else rationalOps.bernLeft col))
noncomputable def halfCoordinate (right : Bool) (x : ℝ) : ℝ := if right then (1+x)/2 else x/2

theorem splitU_eval (p : RationalCube) (nu nv nt : ℕ) (hp : p.Shape nu nv nt)
    (right : Bool) (u v t : ℝ) :
    (p.splitU right).bernEval nu nv nt u v t=p.bernEval nu nv nt (halfCoordinate right u) v t := by
  have hs := (rationalSound.homLift nt t (1-t)).homLift nv v (1-v)
  cases right
  · exact bernLeft_identity hs nu p hp.1 u
  · exact bernRight_identity hs nu p hp.1 u

theorem splitV_eval (p : RationalCube) (nu nv nt : ℕ) (hp : p.Shape nu nv nt)
    (right : Bool) (u v t : ℝ) :
    (p.splitV right).bernEval nu nv nt u v t=p.bernEval nu nv nt u (halfCoordinate right v) t := by
  unfold splitV bernEval
  rw [homogeneous_map]
  apply homogeneous_congr
  intro row hr
  have hs := rationalSound.homLift nt t (1-t)
  cases right
  · exact bernLeft_identity hs nv row (hp.2 row hr).1 v
  · exact bernRight_identity hs nv row (hp.2 row hr).1 v

theorem splitT_eval (p : RationalCube) (nu nv nt : ℕ) (hp : p.Shape nu nv nt)
    (right : Bool) (u v t : ℝ) :
    (p.splitT right).bernEval nu nv nt u v t=p.bernEval nu nv nt u v (halfCoordinate right t) := by
  unfold splitT bernEval
  rw [homogeneous_map]
  apply homogeneous_congr
  intro row hr
  rw [homogeneous_map]
  apply homogeneous_congr
  intro col hc
  cases right
  · exact bernLeft_identity rationalSound nt col ((hp.2 row hr).2 col hc) t
  · exact bernRight_identity rationalSound nt col ((hp.2 row hr).2 col hc) t

theorem bernEval_nonneg (p : RationalCube) (nu nv nt : ℕ) (hc : p.nonnegCheck=true)
    (u v t : ℝ) (hu : 0≤u ∧ u≤1) (hv : 0≤v ∧ v≤1) (ht : 0≤t ∧ t≤1) :
    0≤p.bernEval nu nv nt u v t := by
  have hp := nonnegCheck_sound hc
  apply homogeneous_nonneg _ _ _ _ _ hu.1 (by linarith)
  intro row hr
  apply homogeneous_nonneg _ _ _ _ _ hv.1 (by linarith)
  intro col hcol
  apply homogeneous_nonneg _ _ _ _ _ ht.1 (by linarith)
  exact hp row hr col hcol

/-- The three checked transforms have a single continuous polynomial semantics. -/
theorem bernEval_eq_power (p U V T : RationalCube) (nu nv nt : ℕ)
    (hp : p.Shape nu nv nt) (hUshape : U.Shape nu nv nt) (hVshape : V.Shape nu nv nt)
    (hU : p.bernU.check U=true) (hV : U.bernV.check V=true) (hT : V.bernT.check T=true)
    (u v t : ℝ) : T.bernEval nu nv nt u v t=p.real u v t := by
  have ht : T.bernEval nu nv nt u v t=
      homogeneous (fun row => homogeneous (fun col => horner (fun q : ℚ => (q:ℝ)) col t)
        nv row v (1-v)) nu V u (1-u) := by
    rw [←check_sound hT]
    unfold bernT bernEval
    rw [homogeneous_map]
    apply homogeneous_congr
    intro row hr
    rw [homogeneous_map]
    apply homogeneous_congr
    intro col hc
    exact bernstein_identity rationalSound nt col ((hVshape.2 row hr).2 col hc) t
  rw [ht,←check_sound hV]
  unfold bernV
  rw [homogeneous_map]
  have hv : homogeneous
      (fun row => homogeneous (fun col => horner (fun q : ℚ => (q:ℝ)) col t)
        nv (rationalOps.lift.bernstein row) v (1-v)) nu U u (1-u)=
      homogeneous (fun row => horner (fun col => horner (fun q : ℚ => (q:ℝ)) col t) row v)
        nu U u (1-u) := by
    apply homogeneous_congr
    intro row hr
    exact bernstein_identity (rationalSound.lift t) nv row (hUshape.2 row hr).1 v
  rw [hv,←check_sound hU]
  exact bernstein_identity ((rationalSound.lift t).lift v) nu p hp.1 u

end RationalCube

/-- Order on coefficient lists yields order of their homogeneous evaluations on the positive cone. -/
theorem homogeneous_le {A B : Type} (test : A → B → Bool) (ea : A → ℝ) (eb : B → ℝ)
    (hs : ∀ a b,test a b=true → eb b≤ea a) (n : ℕ) (p : List A) (q : List B)
    (hc : zipCheck test p q=true) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    homogeneous eb n q x y≤homogeneous ea n p x y := by
  induction p generalizing n q with
  | nil => cases q <;> simp_all [zipCheck,homogeneous]
  | cons a p ih =>
    cases q with
    | nil => simp [zipCheck] at hc
    | cons b q =>
      have hh : test a b=true ∧ zipCheck test p q=true := by
        simpa only [zipCheck,Bool.and_eq_true] using hc
      exact add_le_add (mul_le_mul_of_nonneg_right (hs a b hh.1) (pow_nonneg hy _))
        (mul_le_mul_of_nonneg_left (ih (n-1) q hh.2) hx)

end N7.Kernel

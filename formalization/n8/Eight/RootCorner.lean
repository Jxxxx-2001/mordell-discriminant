import Eight.RootTensor.Semantic
import Eight.TensorAssembly

namespace MordellEight.RootCorner

def evalQ {α : Type} (f : α → ℚ) (x : ℚ) : List α → ℚ
  | [] => 0
  | a :: rest => f a + x * evalQ f x rest

theorem evalQ_cast {α : Type} (f : α → ℚ) (g : α → ℝ)
    (h : ∀ a, (f a : ℝ) = g a) (x : ℚ) (p : List α) :
    (evalQ f x p : ℝ) = horner g p (x : ℝ) := by
  induction p with
  | nil => simp [evalQ, horner]
  | cons a p ih => simp [evalQ, horner, h, ih]

def value (u v t : ℚ) := evalQ (evalQ (evalQ id t) v) u RootTensor.lowerPolynomial

theorem value_cast (u v t : ℚ) :
    (value u v t : ℝ) = RootTensor.lowerPolynomial.real u v t := by
  apply evalQ_cast
  intro row
  apply evalQ_cast
  intro col
  exact evalQ_cast id _ (fun _ => rfl) t col

def coord (i : Fin 3) (z : ℚ) : ℚ :=
  (RootTensor.box.hi i - RootTensor.box.lo i) * z + RootTensor.box.lo i

theorem value_minorant (u v t : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t) :
    (value u v t : ℝ) ≤ exactMajorant.real (coord 0 u) (coord 1 v) (coord 2 t) := by
  rw [value_cast, ←RootTensor.bernstein_value]
  simpa only [coord,Rat.cast_add,Rat.cast_mul] using RootTensor.unit_minorant
    (u : ℝ) (v : ℝ) (t : ℝ) (by exact_mod_cast hu) (by exact_mod_cast hv) (by exact_mod_cast ht)

theorem point_bound (u v t a lo hi : ℚ) (n : ℕ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 ≤ t) (ha : 0 < a)
    (hd : 0 < coord 0 u + coord 1 v - 2 * coord 2 t)
    (hc : Checks.logCheck a lo hi n = true)
    (gap : hi - 1 + (coord 0 u + coord 1 v - 2 * coord 2 t) / a ≤ value u v t) :
    Real.log ((coord 0 u : ℝ) + coord 1 v - 2 * coord 2 t) ≤
      exactMajorant.real (coord 0 u) (coord 1 v) (coord 2 t) := by
  have hd' : 0 < (coord 0 u : ℝ) + coord 1 v - 2 * coord 2 t := by exact_mod_cast hd
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  apply (log_le_tangent hd' ha' (Checks.logCheck_sound _ _ _ _ hc).2).trans
  exact le_trans (by exact_mod_cast gap) (value_minorant u v t hu hv ht)

end MordellEight.RootCorner

import N6.CertificateCore
import review.SparseCheck
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Nat.Bitwise


namespace N6.KroneckerCheck
open N6.SparseCheck Polynomial

/-- A single signed integer evaluation suffices when every coefficient is small. -/
theorem root_small {b : ℤ} (hb : b ≠ 0) (p : Polynomial ℤ)
    (bound : ∀ n, (p.coeff n).natAbs < b.natAbs) (hv : p.eval b = 0) : p = 0 := by
  have first (q : Polynomial ℤ) (hq : q.eval b = 0)
      (hc : (q.coeff 0).natAbs < b.natAbs) : q.coeff 0 = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Polynomial.IsRoot.dvd_coeff_zero hq) hc
  have each (n : Nat) : ∀ q : Polynomial ℤ,
      (∀ i, (q.coeff i).natAbs < b.natAbs) → q.eval b = 0 → q.coeff n = 0 := by
    induction n with
    | zero => exact fun q h hq => first q hq (h 0)
    | succ n ih =>
      intro q h hq
      have hc := first q hq (h 0)
      have he := congrArg (Polynomial.eval b) (divX_mul_X_add q)
      simp only [eval_add, eval_mul, eval_X, eval_C, hc, add_zero, hq] at he
      have hd : q.divX.eval b = 0 := (mul_eq_zero.mp he).resolve_right hb
      simpa only [coeff_divX] using ih q.divX (fun i => by simpa only [coeff_divX] using h (i+1)) hd
  ext n
  simpa using each n p bound hv

/-- Linear Kronecker encoding; radix bounds are needed only for the inverse. -/
theorem decode_code (r : Rad) (m : Mon) (h : Fits r m) : decode r (code r m) = m := by
  obtain ⟨hk,he,hc,hb⟩ := h
  have dk : 0 < r.k := Nat.zero_lt_of_lt hk
  have de : 0 < r.e := Nat.zero_lt_of_lt he
  have dc : 0 < r.c := Nat.zero_lt_of_lt hc
  have db : 0 < r.b := Nat.zero_lt_of_lt hb
  cases m
  simp_all [decode, code, Nat.add_mul_div_left, Nat.add_mul_mod_self_left, Nat.div_eq_of_lt,
    Nat.mod_eq_of_lt]

theorem code_plus (r : Rad) (m n : Mon) : code r (m.plus n) = code r m + code r n := by
  simp only [code, Mon.plus]
  ring

noncomputable def formal (r : Rad) : Poly → Polynomial ℤ
  | [] => 0
  | a::p => monomial (code r a.1) a.2 + formal r p

theorem coeff_bound (r : Rad) (p : Poly) (n : Nat) :
    ((formal r p).coeff n).natAbs ≤ mass p := by
  induction p with
  | nil => simp [formal, mass]
  | cons a p ih =>
    simp only [formal, coeff_add, coeff_monomial, mass]
    apply le_trans (Int.natAbs_add_le _ _)
    refine Nat.add_le_add ?_ ih
    split <;> simp

/-- Powers of two are constructed with a kernel natural left shift. -/
theorem place_eq (b n : Nat) : place b n = ((2 : ℤ)^b)^n := by
  simp [place, Nat.shiftLeft_eq, pow_mul]

theorem eval_formal (r : Rad) (bits : Nat) (p : Poly) :
    (formal r p).eval ((2 : ℤ)^bits) = pack r bits p := by
  induction p with
  | nil => simp [formal, pack]
  | cons a p ih => simp only [formal, pack, eval_add, eval_monomial, ih, place_eq]

theorem recovered {R : Type*} [CommRing R] (x : Fin 5 → R) (r : Rad) (p : Poly)
    (fits : ∀ a ∈ p, Fits r a.1) :
    (formal r p).sum (fun n z => (z : R) * monVal x (decode r n)) = value x p := by
  let f : Nat → ℤ → R := fun n z => (z : R) * monVal x (decode r n)
  have fz (i : Nat) : f i 0 = 0 := by simp [f]
  have fa (i : Nat) (u v : ℤ) : f i (u+v) = f i u + f i v := by simp [f, add_mul]
  change (formal r p).sum f = _
  induction p with
  | nil => simp [formal, value, sum_zero_index]
  | cons a p ih =>
    have ha := decode_code r a.1 (fits a (by simp))
    have ht : ∀ a ∈ p, Fits r a.1 := fun t ht => fits t (List.mem_cons_of_mem _ ht)
    rw [formal, sum_add_index _ _ _ fz fa, sum_monomial_index _ _ (fz _), ih ht]
    simp [f, ha, value]

theorem list_sound {R : Type*} [CommRing R] (x : Fin 5 → R) (r : Rad) (bits : Nat) (p : Poly)
    (fits : ∀ a ∈ p, Fits r a.1) (hbound : mass p < ((2 : ℤ)^bits).natAbs)
    (hpack : pack r bits p = 0) : value x p = 0 := by
  have hzero := root_small (pow_ne_zero bits (by decide : (2 : ℤ) ≠ 0)) (formal r p)
    (fun n => lt_of_le_of_lt (coeff_bound r p n) hbound) ((eval_formal r bits p).trans hpack)
  rw [← recovered x r p fits, hzero, sum_zero_index]



theorem fold_raw {A : Type*} [Semiring A] (W : Poly → A) (w : Term → A)
    (hn : W [] = 0) (hc : ∀ a p, W (a::p) = w a + W p)
    (hm : ∀ a b, w (mulTerm a b) = w a * w b) (ps : Products) :
    W (raw ps) = pairs W ps := by
  have happ (p q : Poly) : W (p ++ q) = W p + W q := by
    induction p with
    | nil => simp [hn]
    | cons a p ih => simp only [List.cons_append, hc, ih, add_assoc]
  have hmap (a : Term) (q : Poly) : W (q.map (mulTerm a)) = w a * W q := by
    induction q with
    | nil => simp [hn]
    | cons b q ih => simp only [List.map_cons, hc, hm, ih, mul_add]
  have hflat (p q : Poly) : W (p.flatMap (fun a => q.map (mulTerm a))) = W p * W q := by
    induction p with
    | nil => simp [hn]
    | cons a p ih => simp only [List.flatMap_cons, happ, hmap, ih, hc, add_mul]
  induction ps with
  | nil => exact hn
  | cons z ps ih => simp only [raw, pairs, happ, hflat, ih]

theorem le_upper (f : Mon → Nat) {p : Poly} {a : Term} (h : a ∈ p) : f a.1 ≤ upper f p := by
  induction p with
  | nil => simp at h
  | cons b p ih =>
    rcases List.mem_cons.mp h with rfl|ht
    · exact Nat.le_max_left _ _
    · exact le_trans (ih ht) (Nat.le_max_right _ _)

theorem raw_fits (r : Rad) (ps : Products) (h : roomCheck r ps = true) :
    ∀ a ∈ raw ps, Fits r a.1 := by
  induction ps with
  | nil => simp [raw]
  | cons z ps ih =>
    have hroom : Room r z.1 z.2 ∧ roomCheck r ps = true := by
      simpa [roomCheck] using h
    intro t ht
    simp only [raw, List.mem_append, List.mem_flatMap, List.mem_map] at ht
    rcases ht with ⟨a, ha, b, hb, rfl⟩ | ht
    · have le (f : Mon → Nat) := Nat.add_le_add (le_upper f ha) (le_upper f hb)
      obtain ⟨hk,he,hc,hb'⟩ := hroom.1
      exact ⟨lt_of_le_of_lt (le Mon.k) hk, lt_of_le_of_lt (le Mon.e) he,
        lt_of_le_of_lt (le Mon.c) hc, lt_of_le_of_lt (le Mon.b) hb'⟩
    · exact ih hroom.2 _ ht

/-- All three ground hypotheses touch only the original sparse factors. -/
theorem check {R : Type*} [CommRing R] (x : Fin 5 → R) (r : Rad) (bits : Nat) (ps : Products)
    (hr : roomCheck r ps = true)
    (hn : pairs mass ps < ((2 : ℤ)^bits).natAbs)
    (hz : pairs (pack r bits) ps = 0) : pairs (value x) ps = 0 := by
  have massEq := fold_raw mass (fun a => a.2.natAbs) rfl (fun _ _ => rfl)
    (fun a b => Int.natAbs_mul a.2 b.2) ps
  have packedEq := fold_raw (pack r bits) (fun a => a.2 * place bits (code r a.1))
    rfl (fun _ _ => rfl) (fun a b => by
      simp only [mulTerm, code_plus, place_eq, pow_add]
      ring) ps
  have valEq := fold_raw (value x) (fun a => (a.2 : R) * monVal x a.1)
    rfl (fun _ _ => rfl) (fun a b => by
      simp only [mulTerm, monVal_plus, Int.cast_mul]
      ring) ps
  rw [← valEq]
  exact list_sound x r bits (raw ps) (raw_fits r ps hr) (massEq.trans_lt hn) (packedEq.trans hz)

end N6.KroneckerCheck

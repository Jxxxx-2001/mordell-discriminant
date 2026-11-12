import N6.Weighted49.LexData
import N6.Weighted49.LinearSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
def globalP35 {R : Type*} [CommRing R] (B : R) : R := ∑ i : Fin 36, (row_P35Coefficients i : R)*B^i.val
def coordinate_c {R : Type*} [CommRing R] (B y : R) : R := (lex_cA : R)*y + ∑ i : Fin 35, (lex_cH i : R)*B^i.val
def coordinate_k {R : Type*} [CommRing R] (B y : R) : R := (lex_kA : R)*y + ∑ i : Fin 35, (lex_kH i : R)*B^i.val
def coordinate_e {R : Type*} [CommRing R] (B y : R) : R := (lex_eA : R)*y + ∑ i : Fin 35, (lex_eH i : R)*B^i.val
def row_P35Mon {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 36) : R := x 4 ^ i.val
def row_cMon {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 36) : R := Fin.lastCases (x 3) (fun j : Fin 35 => x 4 ^ j.val) i
def row_kMon {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 36) : R := Fin.lastCases (x 2) (fun j : Fin 35 => x 4 ^ j.val) i
def row_eMon {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 36) : R := Fin.lastCases (x 1) (fun j : Fin 35 => x 4 ^ j.val) i
end N6.Weighted49

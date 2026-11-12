import review.Resultant6Matrix
import N6.CertificateCore
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
def suffixRows0 : Fin 0 → Fin 6 := Fin.elim0
def suffixRows1 : Fin 1 → Fin 6 := ![5]
def suffixRows2 : Fin 2 → Fin 6 := ![4, 5]
def suffixRows3 : Fin 3 → Fin 6 := ![3, 4, 5]
def suffixRows4 : Fin 4 → Fin 6 := ![2, 3, 4, 5]
def suffixRows5 : Fin 5 → Fin 6 := ![1, 2, 3, 4, 5]
def suffixRows6 : Fin 6 → Fin 6 := id
def minorCols000 : Fin 0 → Fin 6 := Fin.elim0
def cut000 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 0) (Fin 0) R :=
  A.submatrix suffixRows0 minorCols000
def minorCols001 : Fin 1 → Fin 6 := ![0]
def cut001 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols001
def minorCols002 : Fin 1 → Fin 6 := ![1]
def cut002 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols002
def minorCols003 : Fin 2 → Fin 6 := ![0, 1]
def cut003 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols003
def minorCols004 : Fin 1 → Fin 6 := ![2]
def cut004 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols004
def minorCols005 : Fin 2 → Fin 6 := ![0, 2]
def cut005 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols005
def minorCols006 : Fin 2 → Fin 6 := ![1, 2]
def cut006 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols006
def minorCols007 : Fin 3 → Fin 6 := ![0, 1, 2]
def cut007 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols007
def minorCols008 : Fin 1 → Fin 6 := ![3]
def cut008 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols008
def minorCols009 : Fin 2 → Fin 6 := ![0, 3]
def cut009 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols009
def minorCols010 : Fin 2 → Fin 6 := ![1, 3]
def cut010 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols010
def minorCols011 : Fin 3 → Fin 6 := ![0, 1, 3]
def cut011 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols011
def minorCols012 : Fin 2 → Fin 6 := ![2, 3]
def cut012 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols012
def minorCols013 : Fin 3 → Fin 6 := ![0, 2, 3]
def cut013 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols013
def minorCols014 : Fin 3 → Fin 6 := ![1, 2, 3]
def cut014 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols014
def minorCols015 : Fin 4 → Fin 6 := ![0, 1, 2, 3]
def cut015 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols015
def minorCols016 : Fin 1 → Fin 6 := ![4]
def cut016 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols016
def minorCols017 : Fin 2 → Fin 6 := ![0, 4]
def cut017 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols017
def minorCols018 : Fin 2 → Fin 6 := ![1, 4]
def cut018 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols018
def minorCols019 : Fin 3 → Fin 6 := ![0, 1, 4]
def cut019 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols019
def minorCols020 : Fin 2 → Fin 6 := ![2, 4]
def cut020 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols020
def minorCols021 : Fin 3 → Fin 6 := ![0, 2, 4]
def cut021 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols021
def minorCols022 : Fin 3 → Fin 6 := ![1, 2, 4]
def cut022 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols022
def minorCols023 : Fin 4 → Fin 6 := ![0, 1, 2, 4]
def cut023 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols023
def minorCols024 : Fin 2 → Fin 6 := ![3, 4]
def cut024 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols024
def minorCols025 : Fin 3 → Fin 6 := ![0, 3, 4]
def cut025 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols025
def minorCols026 : Fin 3 → Fin 6 := ![1, 3, 4]
def cut026 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols026
def minorCols027 : Fin 4 → Fin 6 := ![0, 1, 3, 4]
def cut027 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols027
def minorCols028 : Fin 3 → Fin 6 := ![2, 3, 4]
def cut028 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols028
def minorCols029 : Fin 4 → Fin 6 := ![0, 2, 3, 4]
def cut029 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols029
def minorCols030 : Fin 4 → Fin 6 := ![1, 2, 3, 4]
def cut030 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols030
def minorCols031 : Fin 5 → Fin 6 := ![0, 1, 2, 3, 4]
def cut031 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols031
def minorCols032 : Fin 1 → Fin 6 := ![5]
def cut032 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 1) (Fin 1) R :=
  A.submatrix suffixRows1 minorCols032
def minorCols033 : Fin 2 → Fin 6 := ![0, 5]
def cut033 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols033
def minorCols034 : Fin 2 → Fin 6 := ![1, 5]
def cut034 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols034
def minorCols035 : Fin 3 → Fin 6 := ![0, 1, 5]
def cut035 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols035
def minorCols036 : Fin 2 → Fin 6 := ![2, 5]
def cut036 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols036
def minorCols037 : Fin 3 → Fin 6 := ![0, 2, 5]
def cut037 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols037
def minorCols038 : Fin 3 → Fin 6 := ![1, 2, 5]
def cut038 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols038
def minorCols039 : Fin 4 → Fin 6 := ![0, 1, 2, 5]
def cut039 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols039
def minorCols040 : Fin 2 → Fin 6 := ![3, 5]
def cut040 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols040
def minorCols041 : Fin 3 → Fin 6 := ![0, 3, 5]
def cut041 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols041
def minorCols042 : Fin 3 → Fin 6 := ![1, 3, 5]
def cut042 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols042
def minorCols043 : Fin 4 → Fin 6 := ![0, 1, 3, 5]
def cut043 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols043
def minorCols044 : Fin 3 → Fin 6 := ![2, 3, 5]
def cut044 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols044
def minorCols045 : Fin 4 → Fin 6 := ![0, 2, 3, 5]
def cut045 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols045
def minorCols046 : Fin 4 → Fin 6 := ![1, 2, 3, 5]
def cut046 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols046
def minorCols047 : Fin 5 → Fin 6 := ![0, 1, 2, 3, 5]
def cut047 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols047
def minorCols048 : Fin 2 → Fin 6 := ![4, 5]
def cut048 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 2) (Fin 2) R :=
  A.submatrix suffixRows2 minorCols048
def minorCols049 : Fin 3 → Fin 6 := ![0, 4, 5]
def cut049 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols049
def minorCols050 : Fin 3 → Fin 6 := ![1, 4, 5]
def cut050 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols050
def minorCols051 : Fin 4 → Fin 6 := ![0, 1, 4, 5]
def cut051 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols051
def minorCols052 : Fin 3 → Fin 6 := ![2, 4, 5]
def cut052 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols052
def minorCols053 : Fin 4 → Fin 6 := ![0, 2, 4, 5]
def cut053 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols053
def minorCols054 : Fin 4 → Fin 6 := ![1, 2, 4, 5]
def cut054 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols054
def minorCols055 : Fin 5 → Fin 6 := ![0, 1, 2, 4, 5]
def cut055 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols055
def minorCols056 : Fin 3 → Fin 6 := ![3, 4, 5]
def cut056 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 3) (Fin 3) R :=
  A.submatrix suffixRows3 minorCols056
def minorCols057 : Fin 4 → Fin 6 := ![0, 3, 4, 5]
def cut057 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols057
def minorCols058 : Fin 4 → Fin 6 := ![1, 3, 4, 5]
def cut058 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols058
def minorCols059 : Fin 5 → Fin 6 := ![0, 1, 3, 4, 5]
def cut059 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols059
def minorCols060 : Fin 4 → Fin 6 := ![2, 3, 4, 5]
def cut060 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 4) (Fin 4) R :=
  A.submatrix suffixRows4 minorCols060
def minorCols061 : Fin 5 → Fin 6 := ![0, 2, 3, 4, 5]
def cut061 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols061
def minorCols062 : Fin 5 → Fin 6 := ![1, 2, 3, 4, 5]
def cut062 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 5) (Fin 5) R :=
  A.submatrix suffixRows5 minorCols062
def minorCols063 : Fin 6 → Fin 6 := id
def cut063 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) : Matrix (Fin 6) (Fin 6) R :=
  A.submatrix suffixRows6 minorCols063
end N6.ResultantMinors

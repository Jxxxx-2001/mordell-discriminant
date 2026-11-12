import N6.BQ14.Parents
import N6.Quartics21.Ground001
import N6.Quartics21.Ground002
import N6.Quartics21.Ground003
import N6.Quartics21.Ground004
import N6.Quartics21.Ground005
import N6.Quartics21.Ground006
import N6.Quartics21.Ground007
import N6.Quartics21.Ground008
import N6.Quartics21.Ground009
import N6.Quartics21.Ground010
import N6.Quartics21.Ground011
import N6.Quartics21.Ground012
import N6.Quartics21.Ground013
import N6.Quartics21.Ground014
import N6.Quartics21.Ground015
import N6.Quartics21.Ground016
import N6.Quartics21.Ground017
import N6.Quartics21.Ground018
import N6.Quartics21.Ground019
import N6.Quartics21.Ground020
import N6.Quartics21.Ground021
import N6.Weighted49.ArithmeticCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
def parentData (i : Fin 35) : Poly :=
  match i.val with
  | 0 => N6.Quartics21.Case001.gData
  | 1 => N6.Quartics21.Case002.gData
  | 2 => N6.Quartics21.Case003.gData
  | 3 => N6.Quartics21.Case004.gData
  | 4 => N6.Quartics21.Case005.gData
  | 5 => N6.Quartics21.Case006.gData
  | 6 => N6.Quartics21.Case007.gData
  | 7 => N6.Quartics21.Case008.gData
  | 8 => N6.Quartics21.Case009.gData
  | 9 => N6.Quartics21.Case010.gData
  | 10 => N6.Quartics21.Case011.gData
  | 11 => N6.Quartics21.Case012.gData
  | 12 => N6.Quartics21.Case013.gData
  | 13 => N6.Quartics21.Case014.gData
  | 14 => N6.Quartics21.Case015.gData
  | 15 => N6.Quartics21.Case016.gData
  | 16 => N6.Quartics21.Case017.gData
  | 17 => N6.Quartics21.Case018.gData
  | 18 => N6.Quartics21.Case019.gData
  | 19 => N6.Quartics21.Case020.gData
  | 20 => N6.Quartics21.Case021.gData
  | 21 => N6.BQ14.P022
  | 22 => N6.BQ14.P023
  | 23 => N6.BQ14.P024
  | 24 => N6.BQ14.P025
  | 25 => N6.BQ14.P026
  | 26 => N6.BQ14.P027
  | 27 => N6.BQ14.P028
  | 28 => N6.BQ14.P029
  | 29 => N6.BQ14.P030
  | 30 => N6.BQ14.P031
  | 31 => N6.BQ14.P032
  | 32 => N6.BQ14.P033
  | 33 => N6.BQ14.P034
  | _ => N6.BQ14.P035
def basisMon (i : Fin 49) : Mon :=
  match i.val with
  | 0 => ⟨0,0,0,0,0⟩
  | 1 => ⟨0,1,0,0,0⟩
  | 2 => ⟨0,0,1,0,0⟩
  | 3 => ⟨0,0,0,1,0⟩
  | 4 => ⟨0,0,0,0,1⟩
  | 5 => ⟨0,2,0,0,0⟩
  | 6 => ⟨0,1,1,0,0⟩
  | 7 => ⟨0,1,0,1,0⟩
  | 8 => ⟨0,1,0,0,1⟩
  | 9 => ⟨0,0,2,0,0⟩
  | 10 => ⟨0,0,1,1,0⟩
  | 11 => ⟨0,0,1,0,1⟩
  | 12 => ⟨0,0,0,2,0⟩
  | 13 => ⟨0,0,0,1,1⟩
  | 14 => ⟨0,0,0,0,2⟩
  | 15 => ⟨0,3,0,0,0⟩
  | 16 => ⟨0,2,1,0,0⟩
  | 17 => ⟨0,2,0,1,0⟩
  | 18 => ⟨0,2,0,0,1⟩
  | 19 => ⟨0,1,2,0,0⟩
  | 20 => ⟨0,1,1,1,0⟩
  | 21 => ⟨0,1,1,0,1⟩
  | 22 => ⟨0,1,0,2,0⟩
  | 23 => ⟨0,1,0,1,1⟩
  | 24 => ⟨0,1,0,0,2⟩
  | 25 => ⟨0,0,3,0,0⟩
  | 26 => ⟨0,0,2,1,0⟩
  | 27 => ⟨0,0,2,0,1⟩
  | 28 => ⟨0,0,1,2,0⟩
  | 29 => ⟨0,0,1,1,1⟩
  | 30 => ⟨0,0,1,0,2⟩
  | 31 => ⟨0,0,0,3,0⟩
  | 32 => ⟨0,0,0,2,1⟩
  | 33 => ⟨0,0,0,1,2⟩
  | 34 => ⟨0,0,0,0,3⟩
  | 35 => ⟨0,2,0,0,2⟩
  | 36 => ⟨0,1,1,0,2⟩
  | 37 => ⟨0,1,0,2,1⟩
  | 38 => ⟨0,1,0,1,2⟩
  | 39 => ⟨0,1,0,0,3⟩
  | 40 => ⟨0,0,2,1,1⟩
  | 41 => ⟨0,0,2,0,2⟩
  | 42 => ⟨0,0,1,2,1⟩
  | 43 => ⟨0,0,1,1,2⟩
  | 44 => ⟨0,0,1,0,3⟩
  | 45 => ⟨0,0,0,3,1⟩
  | 46 => ⟨0,0,0,2,2⟩
  | 47 => ⟨0,0,0,1,3⟩
  | _ => ⟨0,0,0,0,4⟩
def basisData (i : Fin 49) : Poly := [(basisMon i,1)]
def scalar (z : Int) : Poly := [(⟨0,0,0,0,0⟩,z)]
end N6.Weighted49

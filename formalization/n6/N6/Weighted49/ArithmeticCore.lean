import N6.CertificateCore

namespace N6.Weighted49

def sumInt : {n : Nat} → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f 0 + sumInt (fun i : Fin n => f i.succ)

def matVec {n : Nat} (M : Fin n → Fin n → Int) (v : Fin n → Int) (i : Fin n) : Int :=
  sumInt (fun j => M i j * v j)

end N6.Weighted49

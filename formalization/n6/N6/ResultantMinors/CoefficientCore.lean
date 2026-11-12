import N6.CertificateCore

namespace N6.ResultantMinors
open N6.SparseCheck

/-- Keep precisely the coefficient of Y^n; Y is the first sparse exponent. -/
def extractY (n : Nat) : Poly → Poly
  | [] => []
  | a :: p =>
    if a.1.t = n then ({ a.1 with t := 0 }, a.2) :: extractY n p
    else extractY n p

end N6.ResultantMinors

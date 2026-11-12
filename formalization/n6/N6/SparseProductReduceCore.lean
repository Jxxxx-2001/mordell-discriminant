import N6.CertificateCore

namespace N6.SparseProductReduce
open N6.SparseCheck N6.KroneckerCheck

/-- Collect the exact sparse convolutions without introducing a positional encoding. -/
def reduceProducts : Products → Poly
  | [] => []
  | z :: ps => merge (mul z.1 z.2) (reduceProducts ps)

end N6.SparseProductReduce

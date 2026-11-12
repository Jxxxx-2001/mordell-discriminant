import Eight.RootGeometry.Boundary
import Eight.RootBounds.B1

namespace MordellEight.RootBounds.B8

theorem majorant : BoxMajorant RootPartition.B8 :=
  RootGeometry.bound8_of_bound1 MordellEight.RootBounds.B1.majorant

#print axioms majorant
end MordellEight.RootBounds.B8

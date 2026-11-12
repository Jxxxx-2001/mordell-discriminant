import Eight.RootGeometry.OrderedFaces
import Eight.RootBounds.B7

namespace MordellEight.RootBounds.B10

theorem majorant : BoxMajorant RootPartition.B10 :=
  RootGeometry.orderedFace_bound RootPartition.B10 RootPartition.B7
    (by decide +kernel) MordellEight.RootBounds.B7.majorant

#print axioms majorant
end MordellEight.RootBounds.B10

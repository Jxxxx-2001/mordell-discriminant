import Eight.RootGeometry.OrderedFaces
import Eight.RootBounds.B17

namespace MordellEight.RootBounds.B24

theorem majorant : BoxMajorant RootPartition.B24 :=
  RootGeometry.orderedFace_bound RootPartition.B24 RootPartition.B17
    (by decide +kernel) MordellEight.RootBounds.B17.majorant

#print axioms majorant
end MordellEight.RootBounds.B24

import Eight.RootNarrowGeometry.B15
import Eight.PackedRoots.B15.C01
import Eight.NarrowPositive.S2L
import Eight.NarrowPositive.S2L0R
import Eight.NarrowPositive.S2L0R1R
import Eight.NarrowPositive.S2L0R1R2R
import Eight.NarrowPositive.S2L0R1R2R0R
import Eight.NarrowPositive.S2L0R1R2R0R1R
import Eight.NarrowPositive.S2L0R1R2R0R1R2L
import Eight.NarrowPositive.S2L0R1R2R0R1R2L0L
import Eight.LocalLeaf

namespace MordellEight.RootBounds.B15
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem majorant : BoxMajorant RootPartition.B15 := by
  apply RootNarrowGeometry.B15.majorant
  · exact NarrowPositive.Row15Leaf0.bound
  · exact NarrowPositive.Row15Leaf1.bound
  · exact NarrowPositive.Row15Leaf2.bound

#print axioms majorant
end MordellEight.RootBounds.B15

import Eight.RootNarrowGeometry.B29
import Eight.PackedRoots.B29.C19
import Eight.LocalLeaf

namespace MordellEight.RootBounds.B29
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem majorant : BoxMajorant RootPartition.B29 := by
  apply RootNarrowGeometry.B29.majorant
  · exact NarrowPositive.Row29Leaf0.bound
  · exact NarrowPositive.Row29Leaf1.bound
  · exact NarrowPositive.Row29Leaf2.bound
  · exact NarrowPositive.Row29Leaf3.bound
  · exact NarrowPositive.Row29Leaf4.bound
  · exact NarrowPositive.Row29Leaf5.bound
  · exact NarrowPositive.Row29Leaf6.bound
  · exact NarrowPositive.Row29Leaf7.bound
  · exact NarrowPositive.Row29Leaf8.bound
  · exact NarrowPositive.Row29Leaf9.bound
  · exact NarrowPositive.Row29Leaf10.bound
  · exact NarrowPositive.Row29Leaf11.bound
  · exact NarrowPositive.Row29Leaf12.bound
  · exact NarrowPositive.Row29Leaf13.bound
  · exact NarrowPositive.Row29Leaf14.bound
  · exact NarrowPositive.Row29Leaf15.bound
  · exact NarrowPositive.Row29Leaf16.bound
  · exact NarrowPositive.Row29Leaf17.bound
  · exact NarrowPositive.Row29Leaf18.bound

#print axioms majorant
end MordellEight.RootBounds.B29

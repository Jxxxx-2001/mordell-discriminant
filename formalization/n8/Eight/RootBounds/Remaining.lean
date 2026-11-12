import Eight.RootBounds.B1
import Eight.RootBounds.B2
import Eight.RootBounds.B3
import Eight.RootBounds.B4
import Eight.RootBounds.B5
import Eight.RootBounds.B6
import Eight.RootBounds.B7
import Eight.RootBounds.B8
import Eight.RootBounds.B10
import Eight.RootBounds.B12
import Eight.RootBounds.B13
import Eight.RootBounds.B14
import Eight.RootBounds.B15
import Eight.RootBounds.B16
import Eight.RootBounds.B17
import Eight.RootBounds.B20
import Eight.RootBounds.B21
import Eight.RootBounds.B22
import Eight.RootBounds.B23
import Eight.RootBounds.B24
import Eight.RootBounds.B28
import Eight.RootBounds.B29
import Eight.RootBounds.B30
import Eight.RootBounds.B31

namespace MordellEight.RootBounds
open RootPartition

theorem domainMajorant :
    DomainMajorant := by
  apply domainMajorant_of_remaining
  intro i
  fin_cases i
  · exact MordellEight.RootBounds.B1.majorant
  · exact MordellEight.RootBounds.B2.majorant
  · exact MordellEight.RootBounds.B3.majorant
  · exact MordellEight.RootBounds.B4.majorant
  · exact MordellEight.RootBounds.B5.majorant
  · exact MordellEight.RootBounds.B6.majorant
  · exact MordellEight.RootBounds.B7.majorant
  · exact MordellEight.RootBounds.B8.majorant
  · exact MordellEight.RootBounds.B10.majorant
  · exact MordellEight.RootBounds.B12.majorant
  · exact MordellEight.RootBounds.B13.majorant
  · exact MordellEight.RootBounds.B14.majorant
  · exact MordellEight.RootBounds.B15.majorant
  · exact MordellEight.RootBounds.B16.majorant
  · exact MordellEight.RootBounds.B17.majorant
  · exact MordellEight.RootBounds.B20.majorant
  · exact MordellEight.RootBounds.B21.majorant
  · exact MordellEight.RootBounds.B22.majorant
  · exact MordellEight.RootBounds.B23.majorant
  · exact MordellEight.RootBounds.B24.majorant
  · exact MordellEight.RootBounds.B28.majorant
  · exact MordellEight.RootBounds.B29.majorant
  · exact MordellEight.RootBounds.B30.majorant
  · exact MordellEight.RootBounds.B31.majorant

#print axioms domainMajorant
end MordellEight.RootBounds

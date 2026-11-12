import N6.Exceptional.Projections
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
def ChartIIIE0Part0 : Poly := [(⟨0,0,1,0,0⟩, 1024), (⟨0,0,5,0,0⟩, -37500), (⟨0,1,3,0,0⟩, 288000), (⟨0,2,1,0,0⟩, -483840), (⟨0,4,1,0,0⟩, 1166400)]
def ChartIIIE0 : Poly := ChartIIIE0Part0
def ChartIIIE1Part0 : Poly := [(⟨0,0,0,0,0⟩, 16384), (⟨0,0,4,0,0⟩, 360000), (⟨0,1,2,0,0⟩, -1382400), (⟨0,2,0,0,0⟩, 663552), (⟨0,4,0,0,0⟩, 3732480)]
def ChartIIIE1 : Poly := ChartIIIE1Part0
def ChartIIIE2Part0 : Poly := [(⟨0,0,3,0,0⟩, -72000), (⟨0,1,1,0,0⟩, 276480), (⟨0,2,3,0,0⟩, -2430000), (⟨0,3,1,0,0⟩, 9331200)]
def ChartIIIE2 : Poly := ChartIIIE2Part0
def ChartIIIE3Part0 : Poly := [(⟨0,0,2,0,0⟩, 307200), (⟨0,1,0,0,0⟩, -1032192), (⟨0,1,4,0,0⟩, 8100000), (⟨0,2,2,0,0⟩, -36288000), (⟨0,3,0,0,0⟩, 24883200)]
def ChartIIIE3 : Poly := ChartIIIE3Part0
def ChartIIIR4Part0 : Poly := [(⟨0,0,0,0,0⟩, 1024), (⟨0,0,4,0,0⟩, -7500), (⟨0,1,2,0,0⟩, 72000), (⟨0,2,0,0,0⟩, -96768), (⟨0,3,2,0,0⟩, 486000), (⟨0,4,0,0,0⟩, -699840)]
def ChartIIIR4 : Poly := ChartIIIR4Part0
def ChartIIIR3Part0 : Poly := [(⟨0,0,3,0,0⟩, 128000), (⟨0,1,1,0,0⟩, -552960), (⟨0,2,3,0,0⟩, -2160000), (⟨0,3,1,0,0⟩, 6220800)]
def ChartIIIR3 : Poly := ChartIIIR3Part0
def ChartIIIDeltaPart0 : Poly := [(⟨0,0,2,0,0⟩, -256), (⟨0,0,6,0,0⟩, -3125), (⟨0,1,0,0,0⟩, 1024), (⟨0,1,4,0,0⟩, 22500), (⟨0,2,2,0,0⟩, -43200), (⟨0,3,0,0,0⟩, 13824), (⟨0,5,0,0,0⟩, 46656)]
def ChartIIIDelta : Poly := ChartIIIDeltaPart0
def ChartIIIUnitM0Part0 : Poly := [(⟨0,0,1,0,0⟩, -2304000), (⟨0,1,3,0,0⟩, -60750000), (⟨0,2,1,0,0⟩, -15552000)]
def ChartIIIUnitM0 : Poly := ChartIIIUnitM0Part0
def ChartIIIUnitM1Part0 : Poly := [(⟨0,0,2,0,0⟩, -816000), (⟨0,1,0,0,0⟩, 3087360), (⟨0,1,4,0,0⟩, -6328125), (⟨0,2,2,0,0⟩, 31185000), (⟨0,3,0,0,0⟩, 8398080)]
def ChartIIIUnitM1 : Poly := ChartIIIUnitM1Part0
def ChartIIIUnitM2Part0 : Poly := [(⟨0,1,1,0,0⟩, -1136640), (⟨0,2,3,0,0⟩, 4050000), (⟨0,3,1,0,0⟩, 1036800)]
def ChartIIIUnitM2 : Poly := ChartIIIUnitM2Part0
def ChartIIIUnitM3Part0 : Poly := [(⟨0,0,0,0,0⟩, -4096), (⟨0,1,2,0,0⟩, -108000), (⟨0,2,0,0,0⟩, -27648)]
def ChartIIIUnitM3 : Poly := ChartIIIUnitM3Part0
def ChartIIIUnitM4Part0 : Poly := [(⟨0,1,0,0,0⟩, 12828672), (⟨0,2,2,0,0⟩, 174960000), (⟨0,3,0,0,0⟩, 44789760)]
def ChartIIIUnitM4 : Poly := ChartIIIUnitM4Part0
def ChartIIIUnitM5Part0 : Poly := [(⟨0,1,1,0,0⟩, 1278720), (⟨0,2,3,0,0⟩, -4556250), (⟨0,3,1,0,0⟩, -1166400)]
def ChartIIIUnitM5 : Poly := ChartIIIUnitM5Part0
def ChartIIIUnitGoalPart0 : Poly := [(⟨0,0,0,0,0⟩, -66355200)]
def ChartIIIUnitGoal : Poly := ChartIIIUnitGoalPart0
def ChartIIIUnitPairs : Products := [(ChartIIIUnitM0, ChartIIIE0), (ChartIIIUnitM1, ChartIIIE1), (ChartIIIUnitM2, ChartIIIE2), (ChartIIIUnitM3, ChartIIIE3), (ChartIIIUnitM4, ChartIIIR4), (ChartIIIUnitM5, ChartIIIR3), (ChartIIIDelta, ChartIIIUnitGoal)]
def ChartIIIUnitRad : Rad := ⟨9,8,1,1⟩
end N6.Exceptional

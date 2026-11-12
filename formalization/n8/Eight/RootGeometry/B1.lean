import Eight.RootGeometry.Common

namespace MordellEight.RootGeometry.B1
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Probe classification: outside; only geometry is certified here. -/
def L0 : ClosedBox 3 := ⟨![(965267/2097152),0,(-965267/524288)],![(965267/1048576),(965267/2097152),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L1 : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-965267/524288)],![(965267/1048576),(965267/1048576),(-2895801/2097152)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L2 : ClosedBox 3 := ⟨![(965267/2097152),(965267/2097152),(-2895801/2097152)],![(2895801/4194304),(965267/1048576),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L3 : ClosedBox 3 := ⟨![(2895801/4194304),(965267/2097152),(-2895801/2097152)],![(965267/1048576),(2895801/4194304),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L4 : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(-2895801/2097152)],![(965267/1048576),(965267/1048576),(-4826335/4194304)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L5 : ClosedBox 3 := ⟨![(2895801/4194304),(2895801/4194304),(-4826335/4194304)],![(6756869/8388608),(965267/1048576),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L6 : ClosedBox 3 := ⟨![(6756869/8388608),(2895801/4194304),(-4826335/4194304)],![(965267/1048576),(6756869/8388608),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L7 : ClosedBox 3 := ⟨![(6756869/8388608),(6756869/8388608),(-4826335/4194304)],![(965267/1048576),(965267/1048576),(-8687403/8388608)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L8 : ClosedBox 3 := ⟨![(6756869/8388608),(6756869/8388608),(-8687403/8388608)],![(14479005/16777216),(965267/1048576),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L9 : ClosedBox 3 := ⟨![(14479005/16777216),(6756869/8388608),(-8687403/8388608)],![(965267/1048576),(14479005/16777216),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L10 : ClosedBox 3 := ⟨![(14479005/16777216),(14479005/16777216),(-8687403/8388608)],![(965267/1048576),(965267/1048576),(-16409539/16777216)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L11 : ClosedBox 3 := ⟨![(14479005/16777216),(14479005/16777216),(-16409539/16777216)],![(29923277/33554432),(965267/1048576),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L12 : ClosedBox 3 := ⟨![(29923277/33554432),(14479005/16777216),(-16409539/16777216)],![(965267/1048576),(29923277/33554432),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L13 : ClosedBox 3 := ⟨![(29923277/33554432),(29923277/33554432),(-16409539/16777216)],![(965267/1048576),(965267/1048576),(-31853811/33554432)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L14 : ClosedBox 3 := ⟨![(29923277/33554432),(29923277/33554432),(-31853811/33554432)],![(60811821/67108864),(965267/1048576),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L15 : ClosedBox 3 := ⟨![(60811821/67108864),(29923277/33554432),(-31853811/33554432)],![(965267/1048576),(60811821/67108864),(-965267/1048576)]⟩

/-- Probe classification: outside; only geometry is certified here. -/
def L16 : ClosedBox 3 := ⟨![(60811821/67108864),(60811821/67108864),(-31853811/33554432)],![(965267/1048576),(965267/1048576),(-62742355/67108864)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L17 : ClosedBox 3 := ⟨![(60811821/67108864),(60811821/67108864),(-62742355/67108864)],![(965267/1048576),(965267/1048576),(-965267/1048576)]⟩

def tree : ClosedTree 3 := .split 1 (965267/2097152) (.leaf 0 L0) (.split 2 (-2895801/2097152) (.leaf 1 L1) (.split 0 (2895801/4194304) (.leaf 2 L2) (.split 1 (2895801/4194304) (.leaf 3 L3) (.split 2 (-4826335/4194304) (.leaf 4 L4) (.split 0 (6756869/8388608) (.leaf 5 L5) (.split 1 (6756869/8388608) (.leaf 6 L6) (.split 2 (-8687403/8388608) (.leaf 7 L7) (.split 0 (14479005/16777216) (.leaf 8 L8) (.split 1 (14479005/16777216) (.leaf 9 L9) (.split 2 (-16409539/16777216) (.leaf 10 L10) (.split 0 (29923277/33554432) (.leaf 11 L11) (.split 1 (29923277/33554432) (.leaf 12 L12) (.split 2 (-31853811/33554432) (.leaf 13 L13) (.split 0 (60811821/67108864) (.leaf 14 L14) (.split 1 (60811821/67108864) (.leaf 15 L15) (.split 2 (-62742355/67108864) (.leaf 16 L16) (.leaf 17 L17)))))))))))))))))

theorem geometry : tree.check RootPartition.B1=true := by decide +kernel

theorem outside0 : outsideCheck L0=true := by decide +kernel

theorem outside1 : outsideCheck L1=true := by decide +kernel

theorem outside2 : outsideCheck L2=true := by decide +kernel

theorem outside3 : outsideCheck L3=true := by decide +kernel

theorem outside4 : outsideCheck L4=true := by decide +kernel

theorem outside5 : outsideCheck L5=true := by decide +kernel

theorem outside6 : outsideCheck L6=true := by decide +kernel

theorem outside7 : outsideCheck L7=true := by decide +kernel

theorem outside8 : outsideCheck L8=true := by decide +kernel

theorem outside9 : outsideCheck L9=true := by decide +kernel

theorem outside10 : outsideCheck L10=true := by decide +kernel

theorem outside11 : outsideCheck L11=true := by decide +kernel

theorem outside12 : outsideCheck L12=true := by decide +kernel

theorem outside13 : outsideCheck L13=true := by decide +kernel

theorem outside14 : outsideCheck L14=true := by decide +kernel

theorem outside15 : outsideCheck L15=true := by decide +kernel

theorem outside16 : outsideCheck L16=true := by decide +kernel

/-- Every non-outside leaf remains an explicit mathematical premise. -/
theorem majorant
    (h17 : BoxMajorant L17)
    : BoxMajorant RootPartition.B1 := by
  apply majorant_of_tree tree RootPartition.B1 geometry
  intro id b hm
  simp only [tree,ClosedTree.leaves,List.mem_append,List.mem_singleton,or_assoc] at hm
  rcases hm with hm0 | hm1 | hm2 | hm3 | hm4 | hm5 | hm6 | hm7 | hm8 | hm9 | hm10 | hm11 | hm12 | hm13 | hm14 | hm15 | hm16 | hm17

  · rcases Prod.mk.inj hm0 with ⟨rfl,rfl⟩
    exact outside_majorant L0 outside0

  · rcases Prod.mk.inj hm1 with ⟨rfl,rfl⟩
    exact outside_majorant L1 outside1

  · rcases Prod.mk.inj hm2 with ⟨rfl,rfl⟩
    exact outside_majorant L2 outside2

  · rcases Prod.mk.inj hm3 with ⟨rfl,rfl⟩
    exact outside_majorant L3 outside3

  · rcases Prod.mk.inj hm4 with ⟨rfl,rfl⟩
    exact outside_majorant L4 outside4

  · rcases Prod.mk.inj hm5 with ⟨rfl,rfl⟩
    exact outside_majorant L5 outside5

  · rcases Prod.mk.inj hm6 with ⟨rfl,rfl⟩
    exact outside_majorant L6 outside6

  · rcases Prod.mk.inj hm7 with ⟨rfl,rfl⟩
    exact outside_majorant L7 outside7

  · rcases Prod.mk.inj hm8 with ⟨rfl,rfl⟩
    exact outside_majorant L8 outside8

  · rcases Prod.mk.inj hm9 with ⟨rfl,rfl⟩
    exact outside_majorant L9 outside9

  · rcases Prod.mk.inj hm10 with ⟨rfl,rfl⟩
    exact outside_majorant L10 outside10

  · rcases Prod.mk.inj hm11 with ⟨rfl,rfl⟩
    exact outside_majorant L11 outside11

  · rcases Prod.mk.inj hm12 with ⟨rfl,rfl⟩
    exact outside_majorant L12 outside12

  · rcases Prod.mk.inj hm13 with ⟨rfl,rfl⟩
    exact outside_majorant L13 outside13

  · rcases Prod.mk.inj hm14 with ⟨rfl,rfl⟩
    exact outside_majorant L14 outside14

  · rcases Prod.mk.inj hm15 with ⟨rfl,rfl⟩
    exact outside_majorant L15 outside15

  · rcases Prod.mk.inj hm16 with ⟨rfl,rfl⟩
    exact outside_majorant L16 outside16

  · rcases Prod.mk.inj hm17 with ⟨rfl,rfl⟩
    exact h17

#print axioms geometry
#print axioms majorant
end MordellEight.RootGeometry.B1

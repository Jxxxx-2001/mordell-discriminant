import Eight.RootGeometry.Narrow

namespace MordellEight.RootNarrowGeometry.B29
open RootGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def box : ClosedBox 3 := narrowBox RootPartition.B29

/-- Probe classification: positive; only geometry is certified here. -/
def L0 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),0],![(6756869/4194304),(6756869/4194304),(965267/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L1 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(965267/4194304)],![(12548471/8388608),(6756869/4194304),(965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L2 : ClosedBox 3 := ⟨![(12548471/8388608),(2895801/2097152),(965267/4194304)],![(6756869/4194304),(6756869/4194304),(965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L3 : ClosedBox 3 := ⟨![(2895801/2097152),(6756869/4194304),0],![(6756869/4194304),(965267/524288),(965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L4 : ClosedBox 3 := ⟨![(6756869/4194304),(2895801/2097152),0],![(965267/524288),(965267/524288),(965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L5 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(965267/2097152)],![(12548471/8388608),(12548471/8388608),(4826335/8388608)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L6 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(4826335/8388608)],![(12548471/8388608),(12548471/8388608),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L7 : ClosedBox 3 := ⟨![(2895801/2097152),(12548471/8388608),(965267/2097152)],![(12548471/8388608),(6756869/4194304),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L8 : ClosedBox 3 := ⟨![(12548471/8388608),(2895801/2097152),(965267/2097152)],![(6756869/4194304),(12548471/8388608),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L9 : ClosedBox 3 := ⟨![(12548471/8388608),(12548471/8388608),(965267/2097152)],![(6756869/4194304),(6756869/4194304),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L10 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(2895801/4194304)],![(12548471/8388608),(12548471/8388608),(965267/1048576)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L11 : ClosedBox 3 := ⟨![(2895801/2097152),(12548471/8388608),(2895801/4194304)],![(12548471/8388608),(6756869/4194304),(965267/1048576)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L12 : ClosedBox 3 := ⟨![(12548471/8388608),(2895801/2097152),(2895801/4194304)],![(6756869/4194304),(6756869/4194304),(965267/1048576)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L13 : ClosedBox 3 := ⟨![(2895801/2097152),(6756869/4194304),(965267/2097152)],![(6756869/4194304),(965267/524288),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L14 : ClosedBox 3 := ⟨![(2895801/2097152),(6756869/4194304),(2895801/4194304)],![(6756869/4194304),(965267/524288),(965267/1048576)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L15 : ClosedBox 3 := ⟨![(6756869/4194304),(2895801/2097152),(965267/2097152)],![(965267/524288),(6756869/4194304),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L16 : ClosedBox 3 := ⟨![(6756869/4194304),(2895801/2097152),(2895801/4194304)],![(965267/524288),(6756869/4194304),(965267/1048576)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L17 : ClosedBox 3 := ⟨![(6756869/4194304),(6756869/4194304),(965267/2097152)],![(965267/524288),(965267/524288),(2895801/4194304)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L18 : ClosedBox 3 := ⟨![(6756869/4194304),(6756869/4194304),(2895801/4194304)],![(965267/524288),(965267/524288),(965267/1048576)]⟩

def tree : ClosedTree 3 := .split 2 (965267/2097152) (.split 0 (6756869/4194304) (.split 1 (6756869/4194304) (.split 2 (965267/4194304) (.leaf 0 L0) (.split 0 (12548471/8388608) (.leaf 1 L1) (.leaf 2 L2))) (.leaf 3 L3)) (.leaf 4 L4)) (.split 0 (6756869/4194304) (.split 1 (6756869/4194304) (.split 2 (2895801/4194304) (.split 0 (12548471/8388608) (.split 1 (12548471/8388608) (.split 2 (4826335/8388608) (.leaf 5 L5) (.leaf 6 L6)) (.leaf 7 L7)) (.split 1 (12548471/8388608) (.leaf 8 L8) (.leaf 9 L9))) (.split 0 (12548471/8388608) (.split 1 (12548471/8388608) (.leaf 10 L10) (.leaf 11 L11)) (.leaf 12 L12))) (.split 2 (2895801/4194304) (.leaf 13 L13) (.leaf 14 L14))) (.split 1 (6756869/4194304) (.split 2 (2895801/4194304) (.leaf 15 L15) (.leaf 16 L16)) (.split 2 (2895801/4194304) (.leaf 17 L17) (.leaf 18 L18))))

theorem geometry : tree.check box=true := by decide +kernel

/-- Every non-outside leaf remains an explicit mathematical premise. -/
theorem majorant
    (h0 : BoxMajorant L0)
    (h1 : BoxMajorant L1)
    (h2 : BoxMajorant L2)
    (h3 : BoxMajorant L3)
    (h4 : BoxMajorant L4)
    (h5 : BoxMajorant L5)
    (h6 : BoxMajorant L6)
    (h7 : BoxMajorant L7)
    (h8 : BoxMajorant L8)
    (h9 : BoxMajorant L9)
    (h10 : BoxMajorant L10)
    (h11 : BoxMajorant L11)
    (h12 : BoxMajorant L12)
    (h13 : BoxMajorant L13)
    (h14 : BoxMajorant L14)
    (h15 : BoxMajorant L15)
    (h16 : BoxMajorant L16)
    (h17 : BoxMajorant L17)
    (h18 : BoxMajorant L18)
    : BoxMajorant RootPartition.B29 := by
  apply majorant_of_narrow RootPartition.B29
  apply majorant_of_tree tree box geometry
  intro id b hm
  simp only [tree,ClosedTree.leaves,List.mem_append,List.mem_singleton,or_assoc] at hm
  rcases hm with hm0 | hm1 | hm2 | hm3 | hm4 | hm5 | hm6 | hm7 | hm8 | hm9 | hm10 | hm11 | hm12 | hm13 | hm14 | hm15 | hm16 | hm17 | hm18

  · rcases Prod.mk.inj hm0 with ⟨rfl,rfl⟩
    exact h0

  · rcases Prod.mk.inj hm1 with ⟨rfl,rfl⟩
    exact h1

  · rcases Prod.mk.inj hm2 with ⟨rfl,rfl⟩
    exact h2

  · rcases Prod.mk.inj hm3 with ⟨rfl,rfl⟩
    exact h3

  · rcases Prod.mk.inj hm4 with ⟨rfl,rfl⟩
    exact h4

  · rcases Prod.mk.inj hm5 with ⟨rfl,rfl⟩
    exact h5

  · rcases Prod.mk.inj hm6 with ⟨rfl,rfl⟩
    exact h6

  · rcases Prod.mk.inj hm7 with ⟨rfl,rfl⟩
    exact h7

  · rcases Prod.mk.inj hm8 with ⟨rfl,rfl⟩
    exact h8

  · rcases Prod.mk.inj hm9 with ⟨rfl,rfl⟩
    exact h9

  · rcases Prod.mk.inj hm10 with ⟨rfl,rfl⟩
    exact h10

  · rcases Prod.mk.inj hm11 with ⟨rfl,rfl⟩
    exact h11

  · rcases Prod.mk.inj hm12 with ⟨rfl,rfl⟩
    exact h12

  · rcases Prod.mk.inj hm13 with ⟨rfl,rfl⟩
    exact h13

  · rcases Prod.mk.inj hm14 with ⟨rfl,rfl⟩
    exact h14

  · rcases Prod.mk.inj hm15 with ⟨rfl,rfl⟩
    exact h15

  · rcases Prod.mk.inj hm16 with ⟨rfl,rfl⟩
    exact h16

  · rcases Prod.mk.inj hm17 with ⟨rfl,rfl⟩
    exact h17

  · rcases Prod.mk.inj hm18 with ⟨rfl,rfl⟩
    exact h18

#print axioms geometry
#print axioms majorant
end MordellEight.RootNarrowGeometry.B29

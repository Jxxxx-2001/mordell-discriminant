import Eight.RootGeometry.Narrow

namespace MordellEight.RootNarrowGeometry.B15
open RootGeometry
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def box : ClosedBox 3 := narrowBox RootPartition.B15

/-- Probe classification: positive; only geometry is certified here. -/
def L0 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(-965267/1048576)],![(6756869/4194304),(965267/524288),(-965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L1 : ClosedBox 3 := ⟨![(6756869/4194304),(2895801/2097152),(-965267/1048576)],![(965267/524288),(965267/524288),(-965267/2097152)]⟩

/-- Probe classification: positive; only geometry is certified here. -/
def L2 : ClosedBox 3 := ⟨![(2895801/2097152),(2895801/2097152),(-965267/2097152)],![(965267/524288),(965267/524288),0]⟩

def tree : ClosedTree 3 := .split 2 (-965267/2097152) (.split 0 (6756869/4194304) (.leaf 0 L0) (.leaf 1 L1)) (.leaf 2 L2)

theorem geometry : tree.check box=true := by decide +kernel

/-- Every non-outside leaf remains an explicit mathematical premise. -/
theorem majorant
    (h0 : BoxMajorant L0)
    (h1 : BoxMajorant L1)
    (h2 : BoxMajorant L2)
    : BoxMajorant RootPartition.B15 := by
  apply majorant_of_narrow RootPartition.B15
  apply majorant_of_tree tree box geometry
  intro id b hm
  simp only [tree,ClosedTree.leaves,List.mem_append,List.mem_singleton,or_assoc] at hm
  rcases hm with hm0 | hm1 | hm2

  · rcases Prod.mk.inj hm0 with ⟨rfl,rfl⟩
    exact h0

  · rcases Prod.mk.inj hm1 with ⟨rfl,rfl⟩
    exact h1

  · rcases Prod.mk.inj hm2 with ⟨rfl,rfl⟩
    exact h2

#print axioms geometry
#print axioms majorant
end MordellEight.RootNarrowGeometry.B15

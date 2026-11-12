import Eight.TensorAssembly
namespace MordellEight.RootPartition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem outside_bound (tree : ClosedTree 3) (b : ClosedBox 3)
    (hg : tree.check b=true) (ho : tree.leaves.all (fun leaf => outsideCheck leaf.2)=true) :
    BoxMajorant b := by
  intro x hx hd
  obtain ⟨id,c,hm,hc⟩ := tree.check_sound b x hg hx
  exact (outsideCheck_sound c (List.all_eq_true.mp ho (id,c) hm) hc hd.1 hd.2).elim

def B0 : ClosedBox 3 := ⟨![0,0,(-965267/524288)],![(965267/2097152),(965267/1048576),(-965267/1048576)]⟩

def B1 : ClosedBox 3 := ⟨![(965267/2097152),0,(-965267/524288)],![(965267/1048576),(965267/1048576),(-965267/1048576)]⟩

def B2 : ClosedBox 3 := ⟨![0,0,(-965267/1048576)],![(965267/2097152),(965267/1048576),0]⟩

def B3 : ClosedBox 3 := ⟨![(965267/2097152),0,(-965267/1048576)],![(965267/1048576),(965267/1048576),0]⟩

def B4 : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/524288)],![(965267/2097152),(965267/524288),(-965267/1048576)]⟩

def B5 : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/524288)],![(965267/1048576),(965267/524288),(-965267/1048576)]⟩

def B6 : ClosedBox 3 := ⟨![0,(965267/1048576),(-965267/1048576)],![(965267/2097152),(965267/524288),0]⟩

def B7 : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(-965267/1048576)],![(965267/1048576),(965267/524288),0]⟩

def B8 : ClosedBox 3 := ⟨![(965267/1048576),0,(-965267/524288)],![(2895801/2097152),(965267/1048576),(-965267/1048576)]⟩

def B9 : ClosedBox 3 := ⟨![(2895801/2097152),0,(-965267/524288)],![(965267/524288),(965267/1048576),(-965267/1048576)]⟩

def B10 : ClosedBox 3 := ⟨![(965267/1048576),0,(-965267/1048576)],![(2895801/2097152),(965267/1048576),0]⟩

def B11 : ClosedBox 3 := ⟨![(2895801/2097152),0,(-965267/1048576)],![(965267/524288),(965267/1048576),0]⟩

def B12 : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/524288)],![(2895801/2097152),(965267/524288),(-965267/1048576)]⟩

def B13 : ClosedBox 3 := ⟨![(2895801/2097152),(965267/1048576),(-965267/524288)],![(965267/524288),(965267/524288),(-965267/1048576)]⟩

def B14 : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(-965267/1048576)],![(2895801/2097152),(965267/524288),0]⟩

def B15 : ClosedBox 3 := ⟨![(2895801/2097152),(965267/1048576),(-965267/1048576)],![(965267/524288),(965267/524288),0]⟩

def B16 : ClosedBox 3 := ⟨![0,0,0],![(965267/2097152),(965267/1048576),(965267/1048576)]⟩

def B17 : ClosedBox 3 := ⟨![(965267/2097152),0,0],![(965267/1048576),(965267/1048576),(965267/1048576)]⟩

def B18 : ClosedBox 3 := ⟨![0,0,(965267/1048576)],![(965267/2097152),(965267/1048576),(965267/524288)]⟩

def B19 : ClosedBox 3 := ⟨![(965267/2097152),0,(965267/1048576)],![(965267/1048576),(965267/1048576),(965267/524288)]⟩

def B20 : ClosedBox 3 := ⟨![0,(965267/1048576),0],![(965267/2097152),(965267/524288),(965267/1048576)]⟩

def B21 : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),0],![(965267/1048576),(965267/524288),(965267/1048576)]⟩

def B22 : ClosedBox 3 := ⟨![0,(965267/1048576),(965267/1048576)],![(965267/2097152),(965267/524288),(965267/524288)]⟩

def B23 : ClosedBox 3 := ⟨![(965267/2097152),(965267/1048576),(965267/1048576)],![(965267/1048576),(965267/524288),(965267/524288)]⟩

def B24 : ClosedBox 3 := ⟨![(965267/1048576),0,0],![(2895801/2097152),(965267/1048576),(965267/1048576)]⟩

def B25 : ClosedBox 3 := ⟨![(2895801/2097152),0,0],![(965267/524288),(965267/1048576),(965267/1048576)]⟩

def B26 : ClosedBox 3 := ⟨![(965267/1048576),0,(965267/1048576)],![(2895801/2097152),(965267/1048576),(965267/524288)]⟩

def B27 : ClosedBox 3 := ⟨![(2895801/2097152),0,(965267/1048576)],![(965267/524288),(965267/1048576),(965267/524288)]⟩

def B28 : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(2895801/2097152),(965267/524288),(965267/1048576)]⟩

def B29 : ClosedBox 3 := ⟨![(2895801/2097152),(965267/1048576),0],![(965267/524288),(965267/524288),(965267/1048576)]⟩

def B30 : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/1048576)],![(2895801/2097152),(965267/524288),(965267/524288)]⟩

def B31 : ClosedBox 3 := ⟨![(2895801/2097152),(965267/1048576),(965267/1048576)],![(965267/524288),(965267/524288),(965267/524288)]⟩

def partition : ClosedTree 3 := .split 2 0 (.split 0 (965267/1048576) (.split 1 (965267/1048576) (.split 2 (-965267/1048576) (.split 0 (965267/2097152) (.leaf 0 B0) (.leaf 1 B1)) (.split 0 (965267/2097152) (.leaf 2 B2) (.leaf 3 B3))) (.split 2 (-965267/1048576) (.split 0 (965267/2097152) (.leaf 4 B4) (.leaf 5 B5)) (.split 0 (965267/2097152) (.leaf 6 B6) (.leaf 7 B7)))) (.split 1 (965267/1048576) (.split 2 (-965267/1048576) (.split 0 (2895801/2097152) (.leaf 8 B8) (.leaf 9 B9)) (.split 0 (2895801/2097152) (.leaf 10 B10) (.leaf 11 B11))) (.split 2 (-965267/1048576) (.split 0 (2895801/2097152) (.leaf 12 B12) (.leaf 13 B13)) (.split 0 (2895801/2097152) (.leaf 14 B14) (.leaf 15 B15))))) (.split 0 (965267/1048576) (.split 1 (965267/1048576) (.split 2 (965267/1048576) (.split 0 (965267/2097152) (.leaf 16 B16) (.leaf 17 B17)) (.split 0 (965267/2097152) (.leaf 18 B18) (.leaf 19 B19))) (.split 2 (965267/1048576) (.split 0 (965267/2097152) (.leaf 20 B20) (.leaf 21 B21)) (.split 0 (965267/2097152) (.leaf 22 B22) (.leaf 23 B23)))) (.split 1 (965267/1048576) (.split 2 (965267/1048576) (.split 0 (2895801/2097152) (.leaf 24 B24) (.leaf 25 B25)) (.split 0 (2895801/2097152) (.leaf 26 B26) (.leaf 27 B27))) (.split 2 (965267/1048576) (.split 0 (2895801/2097152) (.leaf 28 B28) (.leaf 29 B29)) (.split 0 (2895801/2097152) (.leaf 30 B30) (.leaf 31 B31)))))

theorem geometry : partition.check domainBox=true := by decide +kernel
theorem covers (x : Fin 3 → ℝ) (hx : domainBox.Contains x) :
    ∃ id b,(id,b)∈partition.leaves ∧ b.Contains x := partition.check_sound domainBox x geometry hx

def outsideTree0 : ClosedTree 3 := .leaf 0 (⟨![0,0,(-965267/524288)],![(965267/2097152),(965267/1048576),(-965267/1048576)]⟩)
theorem geometry0 : outsideTree0.check B0=true := by decide +kernel
theorem outside0 : outsideTree0.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound0 : BoxMajorant B0 := outside_bound outsideTree0 B0 geometry0 outside0

def outsideTree9 : ClosedTree 3 := .leaf 0 (⟨![(2895801/2097152),0,(-965267/524288)],![(965267/524288),(965267/1048576),(-965267/1048576)]⟩)
theorem geometry9 : outsideTree9.check B9=true := by decide +kernel
theorem outside9 : outsideTree9.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound9 : BoxMajorant B9 := outside_bound outsideTree9 B9 geometry9 outside9

def outsideTree11 : ClosedTree 3 := .leaf 0 (⟨![(2895801/2097152),0,(-965267/1048576)],![(965267/524288),(965267/1048576),0]⟩)
theorem geometry11 : outsideTree11.check B11=true := by decide +kernel
theorem outside11 : outsideTree11.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound11 : BoxMajorant B11 := outside_bound outsideTree11 B11 geometry11 outside11

def outsideTree18 : ClosedTree 3 := .leaf 0 (⟨![0,0,(965267/1048576)],![(965267/2097152),(965267/1048576),(965267/524288)]⟩)
theorem geometry18 : outsideTree18.check B18=true := by decide +kernel
theorem outside18 : outsideTree18.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound18 : BoxMajorant B18 := outside_bound outsideTree18 B18 geometry18 outside18

def outsideTree19 : ClosedTree 3 := .leaf 0 (⟨![(965267/2097152),0,(965267/1048576)],![(965267/1048576),(965267/1048576),(965267/524288)]⟩)
theorem geometry19 : outsideTree19.check B19=true := by decide +kernel
theorem outside19 : outsideTree19.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound19 : BoxMajorant B19 := outside_bound outsideTree19 B19 geometry19 outside19

def outsideTree25 : ClosedTree 3 := .leaf 0 (⟨![(2895801/2097152),0,0],![(965267/524288),(965267/1048576),(965267/1048576)]⟩)
theorem geometry25 : outsideTree25.check B25=true := by decide +kernel
theorem outside25 : outsideTree25.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound25 : BoxMajorant B25 := outside_bound outsideTree25 B25 geometry25 outside25

def outsideTree26 : ClosedTree 3 := .split 1 (965267/2097152) (.leaf 0 (⟨![(965267/1048576),0,(965267/1048576)],![(2895801/2097152),(965267/2097152),(965267/524288)]⟩)) (.split 2 (2895801/2097152) (.split 0 (4826335/4194304) (.leaf 1 (⟨![(965267/1048576),(965267/2097152),(965267/1048576)],![(4826335/4194304),(965267/1048576),(2895801/2097152)]⟩)) (.leaf 2 (⟨![(4826335/4194304),(965267/2097152),(965267/1048576)],![(2895801/2097152),(965267/1048576),(2895801/2097152)]⟩))) (.leaf 3 (⟨![(965267/1048576),(965267/2097152),(2895801/2097152)],![(2895801/2097152),(965267/1048576),(965267/524288)]⟩)))
theorem geometry26 : outsideTree26.check B26=true := by decide +kernel
theorem outside26 : outsideTree26.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound26 : BoxMajorant B26 := outside_bound outsideTree26 B26 geometry26 outside26

def outsideTree27 : ClosedTree 3 := .leaf 0 (⟨![(2895801/2097152),0,(965267/1048576)],![(965267/524288),(965267/1048576),(965267/524288)]⟩)
theorem geometry27 : outsideTree27.check B27=true := by decide +kernel
theorem outside27 : outsideTree27.leaves.all (fun leaf => outsideCheck leaf.2)=true := by decide +kernel
theorem bound27 : BoxMajorant B27 := outside_bound outsideTree27 B27 geometry27 outside27

def knownBox : Fin 8 → ClosedBox 3 := ![B0,B9,B11,B18,B19,B25,B26,B27]

theorem known_majorant (i : Fin 8) : BoxMajorant (knownBox i) := by
  fin_cases i
  · exact bound0
  · exact bound9
  · exact bound11
  · exact bound18
  · exact bound19
  · exact bound25
  · exact bound26
  · exact bound27

def remainingBox : Fin 24 → ClosedBox 3 := ![B1,B2,B3,B4,B5,B6,B7,B8,B10,B12,B13,B14,B15,B16,B17,B20,B21,B22,B23,B24,B28,B29,B30,B31]

/-- The unresolved obligations remain explicit hypotheses, not axioms. -/
theorem domainMajorant_of_remaining
    (bounds : ∀ i : Fin 24, BoxMajorant (remainingBox i)) : DomainMajorant := by
  apply domainMajorant_of_tree partition geometry
  intro id b hm
  simp only [partition,ClosedTree.leaves,List.mem_append,List.mem_singleton,or_assoc] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31

  · rcases Prod.mk.inj h0 with ⟨rfl,rfl⟩
    exact bound0

  · rcases Prod.mk.inj h1 with ⟨rfl,rfl⟩
    exact bounds 0

  · rcases Prod.mk.inj h2 with ⟨rfl,rfl⟩
    exact bounds 1

  · rcases Prod.mk.inj h3 with ⟨rfl,rfl⟩
    exact bounds 2

  · rcases Prod.mk.inj h4 with ⟨rfl,rfl⟩
    exact bounds 3

  · rcases Prod.mk.inj h5 with ⟨rfl,rfl⟩
    exact bounds 4

  · rcases Prod.mk.inj h6 with ⟨rfl,rfl⟩
    exact bounds 5

  · rcases Prod.mk.inj h7 with ⟨rfl,rfl⟩
    exact bounds 6

  · rcases Prod.mk.inj h8 with ⟨rfl,rfl⟩
    exact bounds 7

  · rcases Prod.mk.inj h9 with ⟨rfl,rfl⟩
    exact bound9

  · rcases Prod.mk.inj h10 with ⟨rfl,rfl⟩
    exact bounds 8

  · rcases Prod.mk.inj h11 with ⟨rfl,rfl⟩
    exact bound11

  · rcases Prod.mk.inj h12 with ⟨rfl,rfl⟩
    exact bounds 9

  · rcases Prod.mk.inj h13 with ⟨rfl,rfl⟩
    exact bounds 10

  · rcases Prod.mk.inj h14 with ⟨rfl,rfl⟩
    exact bounds 11

  · rcases Prod.mk.inj h15 with ⟨rfl,rfl⟩
    exact bounds 12

  · rcases Prod.mk.inj h16 with ⟨rfl,rfl⟩
    exact bounds 13

  · rcases Prod.mk.inj h17 with ⟨rfl,rfl⟩
    exact bounds 14

  · rcases Prod.mk.inj h18 with ⟨rfl,rfl⟩
    exact bound18

  · rcases Prod.mk.inj h19 with ⟨rfl,rfl⟩
    exact bound19

  · rcases Prod.mk.inj h20 with ⟨rfl,rfl⟩
    exact bounds 15

  · rcases Prod.mk.inj h21 with ⟨rfl,rfl⟩
    exact bounds 16

  · rcases Prod.mk.inj h22 with ⟨rfl,rfl⟩
    exact bounds 17

  · rcases Prod.mk.inj h23 with ⟨rfl,rfl⟩
    exact bounds 18

  · rcases Prod.mk.inj h24 with ⟨rfl,rfl⟩
    exact bounds 19

  · rcases Prod.mk.inj h25 with ⟨rfl,rfl⟩
    exact bound25

  · rcases Prod.mk.inj h26 with ⟨rfl,rfl⟩
    exact bound26

  · rcases Prod.mk.inj h27 with ⟨rfl,rfl⟩
    exact bound27

  · rcases Prod.mk.inj h28 with ⟨rfl,rfl⟩
    exact bounds 20

  · rcases Prod.mk.inj h29 with ⟨rfl,rfl⟩
    exact bounds 21

  · rcases Prod.mk.inj h30 with ⟨rfl,rfl⟩
    exact bounds 22

  · rcases Prod.mk.inj h31 with ⟨rfl,rfl⟩
    exact bounds 23

#print axioms covers
#print axioms known_majorant
#print axioms domainMajorant_of_remaining
end MordellEight.RootPartition

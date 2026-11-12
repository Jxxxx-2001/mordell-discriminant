import Eight.RootPartition

namespace MordellEight.RootGeometry

theorem outside_majorant (b : ClosedBox 3) (ho : outsideCheck b=true) : BoxMajorant b := by
  intro x hx hd
  exact (outsideCheck_sound b ho hx hd.1 hd.2).elim

theorem majorant_of_tree (tree : ClosedTree 3) (b : ClosedBox 3)
    (hg : tree.check b=true)
    (hleaves : ∀ id c, (id,c) ∈ tree.leaves → BoxMajorant c) : BoxMajorant b := by
  intro x hx hd
  obtain ⟨id,c,hm,hc⟩ := tree.check_sound b x hg hx
  exact hleaves id c hm x hc hd

end MordellEight.RootGeometry

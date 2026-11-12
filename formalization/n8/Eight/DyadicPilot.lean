import Eight.DyadicStages.C8
namespace MordellEight.DyadicPilot


theorem N38.bound : BoxMajorant N38.box := BoxMajorant.join 2 N39.bound N40.bound

theorem N34.bound : BoxMajorant N34.box := BoxMajorant.join 0 N35.bound N36.bound

theorem N33.bound : BoxMajorant N33.box := BoxMajorant.join 2 N34.bound N37.bound

theorem N32.bound : BoxMajorant N32.box := BoxMajorant.join 1 N33.bound N38.bound

theorem N28.bound : BoxMajorant N28.box := BoxMajorant.join 0 N29.bound N30.bound

theorem N27.bound : BoxMajorant N27.box := BoxMajorant.join 2 N28.bound N31.bound

theorem N25.bound : BoxMajorant N25.box := BoxMajorant.join 1 N26.bound N27.bound

theorem N24.bound : BoxMajorant N24.box := BoxMajorant.join 0 N25.bound N32.bound

theorem N20.bound : BoxMajorant N20.box := BoxMajorant.join 0 N21.bound N22.bound

theorem N19.bound : BoxMajorant N19.box := BoxMajorant.join 2 N20.bound N23.bound

theorem N16.bound : BoxMajorant N16.box := BoxMajorant.join 2 N17.bound N18.bound

theorem N15.bound : BoxMajorant N15.box := BoxMajorant.join 1 N16.bound N19.bound

theorem N12.bound : BoxMajorant N12.box := BoxMajorant.join 2 N13.bound N14.bound

theorem N7.bound : BoxMajorant N7.box := BoxMajorant.join 2 N8.bound N9.bound

theorem N6.bound : BoxMajorant N6.box := BoxMajorant.join 1 N7.bound N10.bound

theorem N5.bound : BoxMajorant N5.box := BoxMajorant.join 0 N6.bound N11.bound

theorem N3.bound : BoxMajorant N3.box := BoxMajorant.join 2 N4.bound N5.bound

theorem N2.bound : BoxMajorant N2.box := BoxMajorant.join 1 N3.bound N12.bound

theorem N1.bound : BoxMajorant N1.box := BoxMajorant.join 0 N2.bound N15.bound

theorem N0.bound : BoxMajorant N0.box := BoxMajorant.join 2 N1.bound N24.bound

theorem majorant : BoxMajorant TensorPilotStages.S6.state.box := N0.bound
#print axioms majorant

end MordellEight.DyadicPilot

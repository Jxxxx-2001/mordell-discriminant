import Eight.RootPositive.Root
namespace MordellEight.NarrowPositive.Root
open FixedTensor RationalCube
def controls := RootPositive.Root.controls
def box : ClosedBox 3 := domainBox
theorem valid : TensorMinorant box (decode controls) := RootPositive.Root.valid
theorem widths : box.Widths := RootPositive.Root.widths
theorem shape : (decode controls).shapeCheck 12 12 6=true := RootPositive.Root.shape
end MordellEight.NarrowPositive.Root

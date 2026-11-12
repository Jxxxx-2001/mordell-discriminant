import Eight.CubicBoxes.B28.C43
import Eight.CubicBoxes.B28.C44
import Eight.CubicBoxes.B28.C45
import Eight.CubicBoxes.B28.C46
import Eight.CubicBoxes.B28.C47
import Eight.CubicBoxes.B28.C48
import Eight.CubicBoxes.B28.C49
import Eight.CubicBoxes.B28.C50
import Eight.CubicBoxes.B28.C51
import Eight.CubicBoxes.B28.C52
import Eight.CubicBoxes.B28.C53
import Eight.CubicBoxes.B28.C54
import Eight.CubicBoxes.B28.G00
import Eight.CubicBoxes.B28.G02
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B28
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G254
def box : ClosedBox 3 := ⟨![(965267/1048576),(35714879/33554432),(4826335/8388608)],![(31853811/33554432),(18340073/16777216),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf107.bound
end G254

namespace G255
def box : ClosedBox 3 := ⟨![(965267/1048576),(35714879/33554432),(20270607/33554432)],![(31853811/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf108.bound
end G255

namespace G253
def box : ClosedBox 3 := ⟨![(965267/1048576),(35714879/33554432),(4826335/8388608)],![(31853811/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G254.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G255.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G254.bound) (by rw [eq_true]; exact G255.bound)
end G253

namespace G249
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(31853811/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G250.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G253.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G250.bound) (by rw [eq_true]; exact G253.bound)
end G249

namespace G258
def box : ClosedBox 3 := ⟨![(31853811/33554432),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(35714879/33554432),(20270607/33554432)]⟩
theorem bound : BoxMajorant box := Leaf109.bound
end G258

namespace G259
def box : ClosedBox 3 := ⟨![(31853811/33554432),(8687403/8388608),(20270607/33554432)],![(16409539/16777216),(35714879/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf110.bound
end G259

namespace G257
def box : ClosedBox 3 := ⟨![(31853811/33554432),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(35714879/33554432),(10617937/16777216)]⟩
theorem eq_false : box.half 2 false=G258.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G259.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G258.bound) (by rw [eq_true]; exact G259.bound)
end G257

namespace G260
def box : ClosedBox 3 := ⟨![(31853811/33554432),(35714879/33554432),(4826335/8388608)],![(16409539/16777216),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf111.bound
end G260

namespace G256
def box : ClosedBox 3 := ⟨![(31853811/33554432),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G257.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G260.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G257.bound) (by rw [eq_true]; exact G260.bound)
end G256

namespace G248
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G249.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G256.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G249.bound) (by rw [eq_true]; exact G256.bound)
end G248

namespace G261
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(10617937/16777216)],![(16409539/16777216),(18340073/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf112.bound
end G261

namespace G247
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(18340073/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G248.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G261.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G248.bound) (by rw [eq_true]; exact G261.bound)
end G247

namespace G263
def box : ClosedBox 3 := ⟨![(965267/1048576),(18340073/16777216),(4826335/8388608)],![(16409539/16777216),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf113.bound
end G263

namespace G264
def box : ClosedBox 3 := ⟨![(965267/1048576),(18340073/16777216),(10617937/16777216)],![(16409539/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf114.bound
end G264

namespace G262
def box : ClosedBox 3 := ⟨![(965267/1048576),(18340073/16777216),(4826335/8388608)],![(16409539/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G263.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G264.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G263.bound) (by rw [eq_true]; exact G264.bound)
end G262

namespace G246
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(16409539/16777216),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G247.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G262.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G247.bound) (by rw [eq_true]; exact G262.bound)
end G246

namespace G269
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(4826335/8388608)],![(33784345/33554432),(35714879/33554432),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf115.bound
end G269

namespace G270
def box : ClosedBox 3 := ⟨![(16409539/16777216),(35714879/33554432),(4826335/8388608)],![(33784345/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf116.bound
end G270

namespace G268
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(4826335/8388608)],![(33784345/33554432),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 1 false=G269.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G270.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G269.bound) (by rw [eq_true]; exact G270.bound)
end G268

namespace G271
def box : ClosedBox 3 := ⟨![(33784345/33554432),(8687403/8388608),(4826335/8388608)],![(8687403/8388608),(18340073/16777216),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf117.bound
end G271

namespace G267
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(4826335/8388608)],![(8687403/8388608),(18340073/16777216),(10617937/16777216)]⟩
theorem eq_false : box.half 0 false=G268.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G271.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G268.bound) (by rw [eq_true]; exact G271.bound)
end G267

namespace G272
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(10617937/16777216)],![(8687403/8388608),(18340073/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf118.bound
end G272

namespace G266
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(4826335/8388608)],![(8687403/8388608),(18340073/16777216),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G267.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G272.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G267.bound) (by rw [eq_true]; exact G272.bound)
end G266

namespace G274
def box : ClosedBox 3 := ⟨![(16409539/16777216),(18340073/16777216),(4826335/8388608)],![(8687403/8388608),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf119.bound
end G274

namespace G275
def box : ClosedBox 3 := ⟨![(16409539/16777216),(18340073/16777216),(10617937/16777216)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf120.bound
end G275

namespace G273
def box : ClosedBox 3 := ⟨![(16409539/16777216),(18340073/16777216),(4826335/8388608)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G274.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G275.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G274.bound) (by rw [eq_true]; exact G275.bound)
end G273

namespace G265
def box : ClosedBox 3 := ⟨![(16409539/16777216),(8687403/8388608),(4826335/8388608)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G266.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G273.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G266.bound) (by rw [eq_true]; exact G273.bound)
end G265

namespace G245
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(4826335/8388608)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G246.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G265.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G246.bound) (by rw [eq_true]; exact G265.bound)
end G245

namespace G243
def box : ClosedBox 3 := ⟨![(965267/1048576),(8687403/8388608),(965267/2097152)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G244.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G245.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G244.bound) (by rw [eq_true]; exact G245.bound)
end G243

namespace G13
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(8687403/8388608),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G14.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G243.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G14.bound) (by rw [eq_true]; exact G243.bound)
end G13

namespace G278
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(965267/2097152)],![(4826335/4194304),(8687403/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf121.bound
end G278

namespace G281
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(4826335/8388608)],![(18340073/16777216),(16409539/16777216),(2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G281

namespace G283
def box : ClosedBox 3 := ⟨![(8687403/8388608),(16409539/16777216),(4826335/8388608)],![(18340073/16777216),(8687403/8388608),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf122.bound
end G283

namespace G284
def box : ClosedBox 3 := ⟨![(8687403/8388608),(16409539/16777216),(10617937/16777216)],![(18340073/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf123.bound
end G284

namespace G282
def box : ClosedBox 3 := ⟨![(8687403/8388608),(16409539/16777216),(4826335/8388608)],![(18340073/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G283.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G284.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G283.bound) (by rw [eq_true]; exact G284.bound)
end G282

namespace G280
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(4826335/8388608)],![(18340073/16777216),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G281.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G282.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G281.bound) (by rw [eq_true]; exact G282.bound)
end G280

namespace G285
def box : ClosedBox 3 := ⟨![(18340073/16777216),(965267/1048576),(4826335/8388608)],![(4826335/4194304),(8687403/8388608),(2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G285

namespace G279
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(4826335/8388608)],![(4826335/4194304),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G280.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G285.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G280.bound) (by rw [eq_true]; exact G285.bound)
end G279

namespace G277
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(965267/2097152)],![(4826335/4194304),(8687403/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G278.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G279.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G278.bound) (by rw [eq_true]; exact G279.bound)
end G277

namespace G287
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(965267/2097152)],![(4826335/4194304),(4826335/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf124.bound
end G287

namespace G289
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(4826335/8388608)],![(4826335/4194304),(4826335/4194304),(10617937/16777216)]⟩
theorem bound : BoxMajorant box := Leaf125.bound
end G289

namespace G290
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(10617937/16777216)],![(4826335/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf126.bound
end G290

namespace G288
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(4826335/8388608)],![(4826335/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G289.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G290.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G289.bound) (by rw [eq_true]; exact G290.bound)
end G288

namespace G286
def box : ClosedBox 3 := ⟨![(8687403/8388608),(8687403/8388608),(965267/2097152)],![(4826335/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G287.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G288.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G287.bound) (by rw [eq_true]; exact G288.bound)
end G286

namespace G276
def box : ClosedBox 3 := ⟨![(8687403/8388608),(965267/1048576),(965267/2097152)],![(4826335/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G277.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G286.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G277.bound) (by rw [eq_true]; exact G286.bound)
end G276

namespace G12
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(4826335/4194304),(4826335/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G13.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G276.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G13.bound) (by rw [eq_true]; exact G276.bound)
end G12

namespace G291
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(2895801/4194304)],![(4826335/4194304),(4826335/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf127.bound
end G291

namespace G11
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(4826335/4194304),(4826335/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G12.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G291.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G12.bound) (by rw [eq_true]; exact G291.bound)
end G11

namespace G296
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(965267/2097152)],![(8687403/8388608),(10617937/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf128.bound
end G296

namespace G297
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(4826335/8388608)],![(8687403/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf129.bound
end G297

namespace G295
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(965267/2097152)],![(8687403/8388608),(10617937/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G296.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G297.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G296.bound) (by rw [eq_true]; exact G297.bound)
end G295

namespace G298
def box : ClosedBox 3 := ⟨![(965267/1048576),(10617937/8388608),(965267/2097152)],![(8687403/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf130.bound
end G298

namespace G294
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(965267/2097152)],![(8687403/8388608),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G295.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G298.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G295.bound) (by rw [eq_true]; exact G298.bound)
end G294

namespace G300
def box : ClosedBox 3 := ⟨![(8687403/8388608),(4826335/4194304),(965267/2097152)],![(4826335/4194304),(2895801/2097152),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf131.bound
end G300

namespace G301
def box : ClosedBox 3 := ⟨![(8687403/8388608),(4826335/4194304),(4826335/8388608)],![(4826335/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf132.bound
end G301

namespace G299
def box : ClosedBox 3 := ⟨![(8687403/8388608),(4826335/4194304),(965267/2097152)],![(4826335/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G300.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G301.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G300.bound) (by rw [eq_true]; exact G301.bound)
end G299

namespace G293
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(965267/2097152)],![(4826335/4194304),(2895801/2097152),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G294.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G299.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G294.bound) (by rw [eq_true]; exact G299.bound)
end G293

namespace G302
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(2895801/4194304)],![(4826335/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf133.bound
end G302

namespace G292
def box : ClosedBox 3 := ⟨![(965267/1048576),(4826335/4194304),(965267/2097152)],![(4826335/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G293.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G302.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G293.bound) (by rw [eq_true]; exact G302.bound)
end G292

namespace G10
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(4826335/4194304),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G11.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G292.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G11.bound) (by rw [eq_true]; exact G292.bound)
end G10

namespace G304
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(965267/2097152)],![(2895801/2097152),(4826335/4194304),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf134.bound
end G304

namespace G306
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(965267/2097152)],![(2895801/2097152),(2895801/2097152),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf135.bound
end G306

namespace G307
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(2895801/4194304)],![(2895801/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf136.bound
end G307

namespace G305
def box : ClosedBox 3 := ⟨![(4826335/4194304),(4826335/4194304),(965267/2097152)],![(2895801/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G306.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G307.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G306.bound) (by rw [eq_true]; exact G307.bound)
end G305

namespace G303
def box : ClosedBox 3 := ⟨![(4826335/4194304),(965267/1048576),(965267/2097152)],![(2895801/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G304.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G305.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G304.bound) (by rw [eq_true]; exact G305.bound)
end G303

namespace G9
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),(965267/2097152)],![(2895801/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 0 false=G10.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G303.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G10.bound) (by rw [eq_true]; exact G303.bound)
end G9

namespace G1
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(2895801/2097152),(2895801/2097152),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G2.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G9.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G2.bound) (by rw [eq_true]; exact G9.bound)
end G1

namespace G309
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),0],![(2895801/2097152),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf137.bound
end G309

namespace G311
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(965267/2097152)],![(2895801/2097152),(965267/524288),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf138.bound
end G311

namespace G312
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(2895801/4194304)],![(2895801/2097152),(965267/524288),(965267/1048576)]⟩
theorem bound : BoxMajorant box := Leaf139.bound
end G312

namespace G310
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),(965267/2097152)],![(2895801/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G311.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G312.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G311.bound) (by rw [eq_true]; exact G312.bound)
end G310

namespace G308
def box : ClosedBox 3 := ⟨![(965267/1048576),(2895801/2097152),0],![(2895801/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G309.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G310.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G309.bound) (by rw [eq_true]; exact G310.bound)
end G308

namespace G0
def box : ClosedBox 3 := ⟨![(965267/1048576),(965267/1048576),0],![(2895801/2097152),(965267/524288),(965267/1048576)]⟩
theorem eq_false : box.half 1 false=G1.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G308.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G1.bound) (by rw [eq_true]; exact G308.bound)
end G0

end MordellEight.CubicBoxes.B28

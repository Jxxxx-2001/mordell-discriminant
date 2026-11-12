import Eight.CubicBoxes.B20.C30
import Eight.CubicBoxes.B20.C31
import Eight.CubicBoxes.B20.C32
import Eight.CubicBoxes.B20.C33
import Eight.CubicBoxes.B20.C34
import Eight.CubicBoxes.B20.C35
import Eight.CubicBoxes.B20.C36
import Eight.CubicBoxes.B20.C37
import Eight.CubicBoxes.B20.C38
import Eight.CubicBoxes.B20.C39
import Eight.CubicBoxes.B20.C40
import Eight.CubicBoxes.B20.C41
import Eight.CubicBoxes.B20.C42
import Eight.CubicBoxes.B20.C43
import Eight.CubicBoxes.B20.C44
import Eight.CubicBoxes.B20.G01
import Eight.RootPartition
import Eight.LocalLeaf
namespace MordellEight.CubicBoxes.B20
open FixedTensor IntegerCube RationalCube Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace G165
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),0],![(965267/4194304),(965267/524288),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf78.bound
end G165

namespace G169
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/4194304)],![(965267/8388608),(14479005/8388608),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf79.bound
end G169

namespace G170
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(2895801/8388608)],![(965267/8388608),(14479005/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf80.bound
end G170

namespace G168
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/4194304)],![(965267/8388608),(14479005/8388608),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G169.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G170.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G169.bound) (by rw [eq_true]; exact G170.bound)
end G168

namespace G172
def box : ClosedBox 3 := ⟨![0,(14479005/8388608),(965267/4194304)],![(965267/8388608),(965267/524288),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf81.bound
end G172

namespace G174
def box : ClosedBox 3 := ⟨![0,(14479005/8388608),(2895801/8388608)],![(965267/16777216),(965267/524288),(965267/2097152)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G174

namespace G176
def box : ClosedBox 3 := ⟨![(965267/16777216),(14479005/8388608),(2895801/8388608)],![(965267/8388608),(29923277/16777216),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf82.bound
end G176

namespace G177
def box : ClosedBox 3 := ⟨![(965267/16777216),(29923277/16777216),(2895801/8388608)],![(965267/8388608),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf83.bound
end G177

namespace G175
def box : ClosedBox 3 := ⟨![(965267/16777216),(14479005/8388608),(2895801/8388608)],![(965267/8388608),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G176.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G177.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G176.bound) (by rw [eq_true]; exact G177.bound)
end G175

namespace G173
def box : ClosedBox 3 := ⟨![0,(14479005/8388608),(2895801/8388608)],![(965267/8388608),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G174.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G175.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G174.bound) (by rw [eq_true]; exact G175.bound)
end G173

namespace G171
def box : ClosedBox 3 := ⟨![0,(14479005/8388608),(965267/4194304)],![(965267/8388608),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G172.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G173.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G172.bound) (by rw [eq_true]; exact G173.bound)
end G171

namespace G167
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/4194304)],![(965267/8388608),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G168.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G171.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G168.bound) (by rw [eq_true]; exact G171.bound)
end G167

namespace G179
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/4194304)],![(965267/4194304),(14479005/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf84.bound
end G179

namespace G180
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/4194304)],![(965267/4194304),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf85.bound
end G180

namespace G178
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/4194304)],![(965267/4194304),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G179.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G180.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G179.bound) (by rw [eq_true]; exact G180.bound)
end G178

namespace G166
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/4194304)],![(965267/4194304),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G167.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G178.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G167.bound) (by rw [eq_true]; exact G178.bound)
end G166

namespace G164
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),0],![(965267/4194304),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G165.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G166.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G165.bound) (by rw [eq_true]; exact G166.bound)
end G164

namespace G128
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),0],![(965267/4194304),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G129.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G164.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G129.bound) (by rw [eq_true]; exact G164.bound)
end G128

namespace G183
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),0],![(965267/2097152),(6756869/4194304),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf86.bound
end G183

namespace G186
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/4194304)],![(2895801/8388608),(6756869/4194304),(2895801/8388608)]⟩
theorem bound : BoxMajorant box := Leaf87.bound
end G186

namespace G187
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(2895801/8388608)],![(2895801/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf88.bound
end G187

namespace G185
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/4194304)],![(2895801/8388608),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G186.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G187.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G186.bound) (by rw [eq_true]; exact G187.bound)
end G185

namespace G189
def box : ClosedBox 3 := ⟨![(2895801/8388608),(2895801/2097152),(965267/4194304)],![(965267/2097152),(12548471/8388608),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf89.bound
end G189

namespace G190
def box : ClosedBox 3 := ⟨![(2895801/8388608),(12548471/8388608),(965267/4194304)],![(965267/2097152),(6756869/4194304),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf90.bound
end G190

namespace G188
def box : ClosedBox 3 := ⟨![(2895801/8388608),(2895801/2097152),(965267/4194304)],![(965267/2097152),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G189.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G190.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G189.bound) (by rw [eq_true]; exact G190.bound)
end G188

namespace G184
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),(965267/4194304)],![(965267/2097152),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G185.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G188.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G185.bound) (by rw [eq_true]; exact G188.bound)
end G184

namespace G182
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),0],![(965267/2097152),(6756869/4194304),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G183.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G184.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G183.bound) (by rw [eq_true]; exact G184.bound)
end G182

namespace G192
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),0],![(965267/2097152),(965267/524288),(965267/4194304)]⟩
theorem bound : BoxMajorant box := Leaf91.bound
end G192

namespace G193
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),(965267/4194304)],![(965267/2097152),(965267/524288),(965267/2097152)]⟩
theorem bound : BoxMajorant box := Leaf92.bound
end G193

namespace G191
def box : ClosedBox 3 := ⟨![(965267/4194304),(6756869/4194304),0],![(965267/2097152),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 2 false=G192.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G193.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G192.bound) (by rw [eq_true]; exact G193.bound)
end G191

namespace G181
def box : ClosedBox 3 := ⟨![(965267/4194304),(2895801/2097152),0],![(965267/2097152),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 1 false=G182.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G191.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G182.bound) (by rw [eq_true]; exact G191.bound)
end G181

namespace G127
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),0],![(965267/2097152),(965267/524288),(965267/2097152)]⟩
theorem eq_false : box.half 0 false=G128.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G181.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G128.bound) (by rw [eq_true]; exact G181.bound)
end G127

namespace G198
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/2097152)],![(965267/8388608),(6756869/4194304),(2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G198

namespace G201
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/2097152)],![(965267/4194304),(12548471/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf93.bound
end G201

namespace G202
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(4826335/8388608)],![(965267/4194304),(12548471/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf94.bound
end G202

namespace G200
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/2097152)],![(965267/4194304),(12548471/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G201.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G202.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G201.bound) (by rw [eq_true]; exact G202.bound)
end G200

namespace G206
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/2097152)],![(2895801/16777216),(26062209/16777216),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf95.bound
end G206

namespace G208
def box : ClosedBox 3 := ⟨![(965267/8388608),(26062209/16777216),(965267/2097152)],![(2895801/16777216),(6756869/4194304),(8687403/16777216)]⟩
theorem bound : BoxMajorant box := Leaf96.bound
end G208

namespace G209
def box : ClosedBox 3 := ⟨![(965267/8388608),(26062209/16777216),(8687403/16777216)],![(2895801/16777216),(6756869/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf97.bound
end G209

namespace G207
def box : ClosedBox 3 := ⟨![(965267/8388608),(26062209/16777216),(965267/2097152)],![(2895801/16777216),(6756869/4194304),(4826335/8388608)]⟩
theorem eq_false : box.half 2 false=G208.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G209.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G208.bound) (by rw [eq_true]; exact G209.bound)
end G207

namespace G205
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/2097152)],![(2895801/16777216),(6756869/4194304),(4826335/8388608)]⟩
theorem eq_false : box.half 1 false=G206.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G207.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G206.bound) (by rw [eq_true]; exact G207.bound)
end G205

namespace G210
def box : ClosedBox 3 := ⟨![(2895801/16777216),(12548471/8388608),(965267/2097152)],![(965267/4194304),(6756869/4194304),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf98.bound
end G210

namespace G204
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/2097152)],![(965267/4194304),(6756869/4194304),(4826335/8388608)]⟩
theorem eq_false : box.half 0 false=G205.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G210.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G205.bound) (by rw [eq_true]; exact G210.bound)
end G204

namespace G211
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(4826335/8388608)],![(965267/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf99.bound
end G211

namespace G203
def box : ClosedBox 3 := ⟨![(965267/8388608),(12548471/8388608),(965267/2097152)],![(965267/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G204.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G211.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G204.bound) (by rw [eq_true]; exact G211.bound)
end G203

namespace G199
def box : ClosedBox 3 := ⟨![(965267/8388608),(2895801/2097152),(965267/2097152)],![(965267/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G200.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G203.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G200.bound) (by rw [eq_true]; exact G203.bound)
end G199

namespace G197
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/2097152)],![(965267/4194304),(6756869/4194304),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G198.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G199.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G198.bound) (by rw [eq_true]; exact G199.bound)
end G197

namespace G212
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(2895801/4194304)],![(965267/4194304),(6756869/4194304),(965267/1048576)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G212

namespace G196
def box : ClosedBox 3 := ⟨![0,(2895801/2097152),(965267/2097152)],![(965267/4194304),(6756869/4194304),(965267/1048576)]⟩
theorem eq_false : box.half 2 false=G197.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G212.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G197.bound) (by rw [eq_true]; exact G212.bound)
end G196

namespace G215
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/2097152)],![(965267/8388608),(965267/524288),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf100.bound
end G215

namespace G221
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(2895801/16777216),(27992743/16777216),(8687403/16777216)]⟩
theorem bound : BoxMajorant box := Leaf101.bound
end G221

namespace G222
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(8687403/16777216)],![(2895801/16777216),(27992743/16777216),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf102.bound
end G222

namespace G220
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(2895801/16777216),(27992743/16777216),(4826335/8388608)]⟩
theorem eq_false : box.half 2 false=G221.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G222.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G221.bound) (by rw [eq_true]; exact G222.bound)
end G220

namespace G224
def box : ClosedBox 3 := ⟨![(965267/8388608),(27992743/16777216),(965267/2097152)],![(2895801/16777216),(14479005/8388608),(8687403/16777216)]⟩
theorem bound : BoxMajorant box := Leaf103.bound
end G224

namespace G225
def box : ClosedBox 3 := ⟨![(965267/8388608),(27992743/16777216),(8687403/16777216)],![(2895801/16777216),(14479005/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf104.bound
end G225

namespace G223
def box : ClosedBox 3 := ⟨![(965267/8388608),(27992743/16777216),(965267/2097152)],![(2895801/16777216),(14479005/8388608),(4826335/8388608)]⟩
theorem eq_false : box.half 2 false=G224.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G225.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G224.bound) (by rw [eq_true]; exact G225.bound)
end G223

namespace G219
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(2895801/16777216),(14479005/8388608),(4826335/8388608)]⟩
theorem eq_false : box.half 1 false=G220.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G223.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G220.bound) (by rw [eq_true]; exact G223.bound)
end G219

namespace G226
def box : ClosedBox 3 := ⟨![(2895801/16777216),(6756869/4194304),(965267/2097152)],![(965267/4194304),(14479005/8388608),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf105.bound
end G226

namespace G218
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(965267/4194304),(14479005/8388608),(4826335/8388608)]⟩
theorem eq_false : box.half 0 false=G219.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G226.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G219.bound) (by rw [eq_true]; exact G226.bound)
end G218

namespace G227
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(4826335/8388608)],![(965267/4194304),(14479005/8388608),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf106.bound
end G227

namespace G217
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(965267/4194304),(14479005/8388608),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G218.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G227.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G218.bound) (by rw [eq_true]; exact G227.bound)
end G217

namespace G232
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/2097152)],![(2895801/16777216),(29923277/16777216),(8687403/16777216)]⟩
theorem bound : BoxMajorant box := Leaf107.bound
end G232

namespace G233
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(8687403/16777216)],![(2895801/16777216),(29923277/16777216),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf108.bound
end G233

namespace G231
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/2097152)],![(2895801/16777216),(29923277/16777216),(4826335/8388608)]⟩
theorem eq_false : box.half 2 false=G232.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G233.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G232.bound) (by rw [eq_true]; exact G233.bound)
end G231

namespace G235
def box : ClosedBox 3 := ⟨![(965267/8388608),(29923277/16777216),(965267/2097152)],![(2895801/16777216),(965267/524288),(8687403/16777216)]⟩
theorem bound : BoxMajorant box := Leaf109.bound
end G235

namespace G237
def box : ClosedBox 3 := ⟨![(965267/8388608),(29923277/16777216),(8687403/16777216)],![(4826335/33554432),(965267/524288),(4826335/8388608)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G237

namespace G238
def box : ClosedBox 3 := ⟨![(4826335/33554432),(29923277/16777216),(8687403/16777216)],![(2895801/16777216),(965267/524288),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf110.bound
end G238

namespace G236
def box : ClosedBox 3 := ⟨![(965267/8388608),(29923277/16777216),(8687403/16777216)],![(2895801/16777216),(965267/524288),(4826335/8388608)]⟩
theorem eq_false : box.half 0 false=G237.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G238.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G237.bound) (by rw [eq_true]; exact G238.bound)
end G236

namespace G234
def box : ClosedBox 3 := ⟨![(965267/8388608),(29923277/16777216),(965267/2097152)],![(2895801/16777216),(965267/524288),(4826335/8388608)]⟩
theorem eq_false : box.half 2 false=G235.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G236.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G235.bound) (by rw [eq_true]; exact G236.bound)
end G234

namespace G230
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/2097152)],![(2895801/16777216),(965267/524288),(4826335/8388608)]⟩
theorem eq_false : box.half 1 false=G231.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G234.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G231.bound) (by rw [eq_true]; exact G234.bound)
end G230

namespace G239
def box : ClosedBox 3 := ⟨![(2895801/16777216),(14479005/8388608),(965267/2097152)],![(965267/4194304),(965267/524288),(4826335/8388608)]⟩
theorem bound : BoxMajorant box := Leaf111.bound
end G239

namespace G229
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/2097152)],![(965267/4194304),(965267/524288),(4826335/8388608)]⟩
theorem eq_false : box.half 0 false=G230.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G239.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G230.bound) (by rw [eq_true]; exact G239.bound)
end G229

namespace G241
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(4826335/8388608)],![(2895801/16777216),(965267/524288),(2895801/4194304)]⟩
theorem checked : outsideCheck box=true := by decide +kernel
theorem bound : BoxMajorant box := by
  intro x hx hd
  exact (outsideCheck_sound box checked hx hd.1 hd.2).elim
end G241

namespace G243
def box : ClosedBox 3 := ⟨![(2895801/16777216),(14479005/8388608),(4826335/8388608)],![(965267/4194304),(29923277/16777216),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf112.bound
end G243

namespace G244
def box : ClosedBox 3 := ⟨![(2895801/16777216),(29923277/16777216),(4826335/8388608)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem bound : BoxMajorant box := Leaf113.bound
end G244

namespace G242
def box : ClosedBox 3 := ⟨![(2895801/16777216),(14479005/8388608),(4826335/8388608)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G243.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G244.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G243.bound) (by rw [eq_true]; exact G244.bound)
end G242

namespace G240
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(4826335/8388608)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G241.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G242.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G241.bound) (by rw [eq_true]; exact G242.bound)
end G240

namespace G228
def box : ClosedBox 3 := ⟨![(965267/8388608),(14479005/8388608),(965267/2097152)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 2 false=G229.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 2 true=G240.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 2
  (by rw [eq_false]; exact G229.bound) (by rw [eq_true]; exact G240.bound)
end G228

namespace G216
def box : ClosedBox 3 := ⟨![(965267/8388608),(6756869/4194304),(965267/2097152)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 1 false=G217.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 1 true=G228.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 1
  (by rw [eq_false]; exact G217.bound) (by rw [eq_true]; exact G228.bound)
end G216

namespace G214
def box : ClosedBox 3 := ⟨![0,(6756869/4194304),(965267/2097152)],![(965267/4194304),(965267/524288),(2895801/4194304)]⟩
theorem eq_false : box.half 0 false=G215.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem eq_true : box.half 0 true=G216.box := by
  apply congrArg₂ ClosedBox.mk <;> funext i <;> fin_cases i <;> decide +kernel
theorem bound : BoxMajorant box := BoxMajorant.join 0
  (by rw [eq_false]; exact G215.bound) (by rw [eq_true]; exact G216.bound)
end G214

end MordellEight.CubicBoxes.B20

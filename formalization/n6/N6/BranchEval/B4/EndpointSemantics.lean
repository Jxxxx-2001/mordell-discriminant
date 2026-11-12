import N6.BranchEval.B4.EndpointDefinitions
import N6.BranchEval.B4.ProgramChecked
import N6.BranchEval.B4.ProgramBindingProbeGround
import Mathlib.Tactic.NormNum
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace N6.BranchEval.B4.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
variable {K : Type*} [Field K] [CharZero K]
theorem program_law (x : Fin 5 → K) (hf : value x program.factor = 0) (i : Nat) (hi : i < program.size) : nodeValue x program i = opValue x program (program.row i).op := checkAt_sound x program i hf (checked_program i hi)
theorem atom_B (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 0 = B x := by
  have h := program_law x hf 0 (by decide)
  change nodeValue x program 0 = B x at h
  exact h
theorem atom_C (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 1 = C x := by
  have h := program_law x hf 1 (by decide)
  change nodeValue x program 1 = C x at h
  exact h
theorem atom_Kcoord (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 2 = Kcoord x := by
  have h := program_law x hf 2 (by decide)
  change nodeValue x program 2 = Kcoord x at h
  exact h
theorem atom_E (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 3 = E x := by
  have h := program_law x hf 3 (by decide)
  change nodeValue x program 3 = E x at h
  exact h
theorem atom_Di (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 406 = Di x := by
  have h := program_law x hf 406 (by decide)
  change nodeValue x program 406 = Di x at h
  exact h
theorem atom_Ri (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 796 = Ri x := by
  have h := program_law x hf 796 (by decide)
  change nodeValue x program 796 = Ri x at h
  exact h
theorem atom_Ay (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 797 = Ay x := by
  have h := program_law x hf 797 (by decide)
  change nodeValue x program 797 = Ay x at h
  exact h
theorem originalD_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program originalDExpr = originalD (B x) (C x) (Kcoord x) (E x) := by
  simp only [originalDExpr, e0405, e0404, e0403, e0402, e0401, e0400, e0399, e0398, e0397, e0396, e0395, e0394, e0393, e0392, e0391, e0390, e0389, e0388, e0387, e0386, e0385, e0384, e0383, e0382, e0381, e0380, e0379, e0378, e0377, e0376, e0375, e0374, e0373, e0372, e0371, e0370, e0369, e0368, e0367, e0366, e0365, e0364, e0363, e0362, e0361, e0360, e0359, e0358, e0357, e0356, e0355, e0354, e0353, e0352, e0351, e0350, e0349, e0348, e0347, e0346, e0345, e0344, e0343, e0342, e0341, e0340, e0339, e0338, e0337, e0336, e0335, e0334, e0333, e0332, e0331, e0330, e0329, e0328, e0327, e0326, e0325, e0324, e0323, e0322, e0321, e0320, e0319, e0318, e0317, e0316, e0315, e0314, e0313, e0312, e0311, e0310, e0309, e0308, e0307, e0306, e0305, e0304, e0303, e0302, e0301, e0300, e0299, e0298, e0297, e0296, e0295, e0294, e0293, e0292, e0291, e0290, e0289, e0288, e0287, e0286, e0285, e0284, e0283, e0282, e0281, e0280, e0279, e0278, e0277, e0276, e0275, e0274, e0273, e0272, e0271, e0270, e0269, e0268, e0267, e0266, e0265, e0264, e0263, e0262, e0261, e0260, e0259, e0258, e0257, e0256, e0255, e0254, e0253, e0252, e0251, e0250, e0249, e0248, e0247, e0246, e0245, e0244, e0243, e0242, e0241, e0240, e0239, e0238, e0237, e0236, e0235, e0234, e0233, e0232, e0231, e0230, e0229, e0228, e0227, e0226, e0225, e0224, e0223, e0222, e0221, e0220, e0219, e0218, e0217, e0216, e0215, e0214, e0213, e0212, e0211, e0210, e0209, e0208, e0207, e0206, e0205, e0204, e0203, e0202, e0201, e0200, e0199, e0198, e0197, e0196, e0195, e0194, e0193, e0192, e0191, e0190, e0189, e0188, e0187, e0186, e0185, e0184, e0183, e0182, e0181, e0180, e0179, e0178, e0177, e0176, e0175, e0174, e0173, e0172, e0171, e0170, e0169, e0168, e0167, e0166, e0165, e0164, e0163, e0162, e0161, e0160, e0159, e0158, e0157, e0156, e0155, e0154, e0153, e0152, e0151, e0150, e0149, e0148, e0147, e0146, e0145, e0144, e0143, e0142, e0141, e0140, e0139, e0138, e0137, e0136, e0135, e0134, e0133, e0132, e0131, e0130, e0129, e0128, e0127, e0126, e0125, e0124, e0123, e0122, e0121, e0120, e0119, e0118, e0117, e0116, e0115, e0114, e0113, e0112, e0111, e0110, e0109, e0108, e0107, e0106, e0105, e0104, e0103, e0102, e0101, e0100, e0099, e0098, e0097, e0096, e0095, e0094, e0093, e0092, e0091, e0090, e0089, e0088, e0087, e0086, e0085, e0084, e0083, e0082, e0081, e0080, e0079, e0078, e0077, e0076, e0075, e0074, e0073, e0072, e0071, e0070, e0069, e0068, e0067, e0066, e0065, e0064, e0063, e0062, e0061, e0060, e0059, e0058, e0057, e0056, e0055, e0054, e0053, e0052, e0051, e0050, e0049, e0048, e0047, e0046, e0045, e0044, e0043, e0042, e0041, e0040, e0039, e0038, e0037, e0036, e0035, e0034, e0033, e0032, e0031, e0030, e0029, e0028, e0027, e0026, e0025, e0024, e0023, e0022, e0021, e0020, e0019, e0018, e0017, e0016, e0015, e0014, e0013, e0012, e0011, e0010, e0009, e0008, e0007, e0006, e0005, e0004, e0003, e0002, e0001, e0000, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_B : B x = q_B
  all_goals generalize h_C : C x = q_C
  all_goals generalize h_Kcoord : Kcoord x = q_Kcoord
  all_goals generalize h_E : E x = q_E
  all_goals (norm_num [originalD] <;> ring)
#print axioms originalD_expr_value
theorem originalR4_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program originalR4Expr = originalR4 (B x) (C x) (Kcoord x) (E x) := by
  simp only [originalR4Expr, e0794, e0793, e0792, e0791, e0790, e0789, e0788, e0787, e0786, e0785, e0784, e0783, e0782, e0781, e0780, e0779, e0778, e0777, e0776, e0775, e0774, e0773, e0772, e0771, e0770, e0769, e0768, e0767, e0766, e0765, e0764, e0763, e0762, e0761, e0760, e0759, e0758, e0757, e0756, e0755, e0754, e0753, e0752, e0751, e0750, e0749, e0748, e0747, e0746, e0745, e0744, e0743, e0742, e0741, e0740, e0739, e0738, e0737, e0736, e0735, e0734, e0733, e0732, e0731, e0730, e0729, e0728, e0727, e0726, e0725, e0724, e0723, e0722, e0721, e0720, e0719, e0718, e0717, e0716, e0715, e0714, e0713, e0712, e0711, e0710, e0709, e0708, e0707, e0706, e0705, e0704, e0703, e0702, e0701, e0700, e0699, e0698, e0697, e0696, e0695, e0694, e0693, e0692, e0691, e0690, e0689, e0688, e0687, e0686, e0685, e0684, e0683, e0682, e0681, e0680, e0679, e0678, e0677, e0676, e0675, e0674, e0673, e0672, e0671, e0670, e0669, e0668, e0667, e0666, e0665, e0664, e0663, e0662, e0661, e0660, e0659, e0658, e0657, e0656, e0655, e0654, e0653, e0652, e0651, e0650, e0649, e0648, e0647, e0646, e0645, e0644, e0643, e0642, e0641, e0640, e0639, e0638, e0637, e0636, e0635, e0634, e0633, e0632, e0631, e0630, e0629, e0628, e0627, e0626, e0625, e0624, e0623, e0622, e0621, e0620, e0619, e0618, e0617, e0616, e0615, e0614, e0613, e0612, e0611, e0610, e0609, e0608, e0607, e0606, e0605, e0604, e0603, e0602, e0601, e0600, e0599, e0598, e0597, e0596, e0595, e0594, e0593, e0592, e0591, e0590, e0589, e0588, e0587, e0586, e0585, e0584, e0583, e0582, e0581, e0580, e0579, e0578, e0577, e0576, e0575, e0574, e0573, e0572, e0571, e0570, e0569, e0568, e0567, e0566, e0565, e0564, e0563, e0562, e0561, e0560, e0559, e0558, e0557, e0556, e0555, e0554, e0553, e0552, e0551, e0550, e0549, e0548, e0547, e0546, e0545, e0544, e0543, e0542, e0541, e0540, e0539, e0538, e0537, e0536, e0535, e0534, e0533, e0532, e0531, e0530, e0529, e0528, e0527, e0526, e0525, e0524, e0523, e0522, e0521, e0520, e0519, e0518, e0517, e0516, e0515, e0514, e0513, e0512, e0511, e0510, e0509, e0508, e0507, e0506, e0505, e0504, e0503, e0502, e0501, e0500, e0499, e0498, e0497, e0496, e0495, e0494, e0493, e0492, e0491, e0490, e0489, e0488, e0487, e0486, e0485, e0484, e0483, e0482, e0481, e0480, e0479, e0478, e0477, e0476, e0475, e0474, e0473, e0472, e0471, e0470, e0469, e0468, e0467, e0466, e0465, e0464, e0463, e0462, e0461, e0460, e0459, e0458, e0457, e0456, e0455, e0454, e0453, e0452, e0451, e0450, e0449, e0448, e0447, e0446, e0445, e0444, e0443, e0442, e0441, e0440, e0439, e0438, e0437, e0436, e0435, e0434, e0433, e0432, e0431, e0430, e0429, e0428, e0427, e0426, e0425, e0424, e0423, e0422, e0421, e0420, e0419, e0418, e0417, e0416, e0415, e0414, e0413, e0412, e0411, e0410, e0409, e0408, e0407, e0406, e0370, e0360, e0356, e0355, e0327, e0326, e0325, e0270, e0269, e0254, e0228, e0227, e0215, e0214, e0183, e0169, e0093, e0087, e0077, e0076, e0071, e0040, e0029, e0016, e0014, e0011, e0010, e0008, e0007, e0005, e0004, e0003, e0002, e0001, e0000, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_B : B x = q_B
  all_goals generalize h_C : C x = q_C
  all_goals generalize h_Kcoord : Kcoord x = q_Kcoord
  all_goals generalize h_E : E x = q_E
  all_goals (norm_num [originalR4] <;> ring)
#print axioms originalR4_expr_value
theorem HofAy_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program HofAyExpr = H (Ay x) := by
  simp only [HofAyExpr, e0833, e0832, e0831, e0830, e0829, e0828, e0827, e0826, e0825, e0824, e0823, e0822, e0821, e0820, e0819, e0818, e0817, e0816, e0815, e0814, e0813, e0812, e0811, e0810, e0809, e0808, e0807, e0806, e0805, e0804, e0803, e0802, e0801, e0800, e0799, e0798, e0797, e0795, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_Ay : Ay x = q_Ay
  all_goals (norm_num [H, ratEval, hCoefficients, List.foldr] <;> ring)
#print axioms HofAy_expr_value
theorem BofAy_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program BofAyExpr = B_from_Ay (Ay x) := by
  simp only [BofAyExpr, e0865, e0864, e0863, e0862, e0861, e0860, e0859, e0858, e0857, e0856, e0855, e0854, e0853, e0852, e0851, e0850, e0849, e0848, e0847, e0846, e0845, e0844, e0843, e0842, e0841, e0840, e0839, e0838, e0837, e0836, e0835, e0834, e0798, e0797, e0795, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_Ay : Ay x = q_Ay
  all_goals (norm_num [B_from_Ay, ratEval, bCoefficients, List.foldr] <;> ring)
#print axioms BofAy_expr_value
theorem VofAy_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program VofAyExpr = V (Ay x) := by
  simp only [VofAyExpr, e0897, e0896, e0895, e0894, e0893, e0892, e0891, e0890, e0889, e0888, e0887, e0886, e0885, e0884, e0883, e0882, e0881, e0880, e0879, e0878, e0877, e0876, e0875, e0874, e0873, e0872, e0871, e0870, e0869, e0868, e0867, e0866, e0798, e0797, e0795, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_Ay : Ay x = q_Ay
  all_goals (norm_num [V, ratEval, vCoefficients, List.foldr] <;> ring)
#print axioms VofAy_expr_value
theorem physicalSquare_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program physicalSquareExpr = physicalSquare (Ay x) (Di x) := by
  simp only [physicalSquareExpr, e0907, e0906, e0905, e0904, e0903, e0902, e0901, e0900, e0899, e0898, e0796, e0795, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_Di : Di x = q_Di
  all_goals generalize h_Ay : Ay x = q_Ay
  all_goals (norm_num [physicalSquare] <;> ring)
#print axioms physicalSquare_expr_value
theorem DiTimesAy_expr_value (x : Fin 5 → K) (hf : value x program.factor = 0) : exprValue x program DiTimesAyExpr = Di x * Ay x := by
  simp only [DiTimesAyExpr, e0908, e0796, e0795, exprValue, literal_field, atom_B x hf, atom_C x hf, atom_Kcoord x hf, atom_E x hf, atom_Di x hf, atom_Ri x hf, atom_Ay x hf]
  all_goals generalize h_Di : Di x = q_Di
  all_goals generalize h_Ay : Ay x = q_Ay
  all_goals (norm_num [] <;> ring)
#print axioms DiTimesAy_expr_value
theorem zero_node (x : Fin 5 → K) (hf : value x program.factor = 0) : nodeValue x program 799 = 0 := by
  have h := matchesExpr_sound x program (program_law x hf) (.lit 0 1) 799 zero_binding
  simpa [exprValue, literal_field] using h
theorem endpoint00 (x : Fin 5 → K) (hf : value x program.factor = 0) : originalD (B x) (C x) (Kcoord x) (E x) = Di x := by
  have hl := matchesExpr_sound x program (program_law x hf) originalDExpr 405 originalD_binding
  have hn : nodeValue x program 405 = nodeValue x program 406 := congrArg (meaning x) endpoint00_same_nf
  rw [originalD_expr_value x hf] at hl
  exact hl.symm.trans (hn.trans (atom_Di x hf))
theorem endpoint01 (x : Fin 5 → K) (hf : value x program.factor = 0) : originalR4 (B x) (C x) (Kcoord x) (E x) = Ri x := by
  have hl := matchesExpr_sound x program (program_law x hf) originalR4Expr 795 originalR4_binding
  have hn : nodeValue x program 795 = nodeValue x program 796 := congrArg (meaning x) endpoint01_same_nf
  rw [originalR4_expr_value x hf] at hl
  exact hl.symm.trans (hn.trans (atom_Ri x hf))
theorem endpoint02 (x : Fin 5 → K) (hf : value x program.factor = 0) : Di x * Ay x = Ri x := by
  have hl := matchesExpr_sound x program (program_law x hf) DiTimesAyExpr 798 DiTimesAy_binding
  have hn : nodeValue x program 798 = nodeValue x program 796 := congrArg (meaning x) endpoint02_same_nf
  rw [DiTimesAy_expr_value x hf] at hl
  exact hl.symm.trans (hn.trans (atom_Ri x hf))
theorem endpoint03 (x : Fin 5 → K) (hf : value x program.factor = 0) : H (Ay x) = 0 := by
  have hl := matchesExpr_sound x program (program_law x hf) HofAyExpr 835 HofAy_binding
  have hn : nodeValue x program 835 = nodeValue x program 799 := congrArg (meaning x) endpoint03_same_nf
  rw [HofAy_expr_value x hf] at hl
  exact hl.symm.trans (hn.trans (zero_node x hf))
theorem endpoint04 (x : Fin 5 → K) (hf : value x program.factor = 0) : B_from_Ay (Ay x) = B x := by
  have hl := matchesExpr_sound x program (program_law x hf) BofAyExpr 867 BofAy_binding
  have hn : nodeValue x program 867 = nodeValue x program 0 := congrArg (meaning x) endpoint04_same_nf
  rw [BofAy_expr_value x hf] at hl
  exact hl.symm.trans (hn.trans (atom_B x hf))
theorem endpoint05 (x : Fin 5 → K) (hf : value x program.factor = 0) : V (Ay x) = physicalSquare (Ay x) (Di x) := by
  have h := checked_endpoint x program hf checked_program 899 909 VofAyExpr physicalSquareExpr VofAy_binding physicalSquare_binding endpoint05_same_nf
  simpa only [VofAy_expr_value x hf, physicalSquare_expr_value x hf] using h
#print axioms endpoint05
end N6.BranchEval.B4.ProgramData

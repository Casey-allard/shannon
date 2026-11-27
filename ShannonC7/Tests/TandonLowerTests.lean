import ShannonC7.TandonLower

namespace ShannonC7.Tests

-- Verify numerical targets and constants
example : c7_lower_num_m1 = 3258835618853760 := rfl
example : c7_lower_den_m1 = 1000000000000000 := rfl
example : (c7_lower_num_m1 : ℚ) / (c7_lower_den_m1 : ℚ) = 3258835618853760 / 1000000000000000 := by norm_num [c7_lower_num_m1, c7_lower_den_m1]

-- Verify Subst / Code list validity certificates and Algebraic HetGao contracts
#check BPZTables.T2a_ok
#check BPZTables.T3b_ok
#check BPZTables.C4a_ok
#check BPZTables.S2a
#check BPZTables.S3b
#check BPZTables.K4a
#check w_hetGao
#check hetGao_P_O_eq
#check w_multiSubst_ofLists
#check le_indepNum_multiCode_ofList

-- Verify base 5D weights and block-signature certificates C1, C2, C4
example : baseR5.w .B = 359 ∧ baseR5.w .N = 322 := ⟨baseR5_w.1, baseR5_w.2.1⟩
example : (strongPowPi C7 10).IsIndepSet (J10_out : Set (Fin 10 → ZMod 7)) := J10_out_indep
example : (strongPowPi C7 15).IsIndepSet (J15_out : Set (Fin 15 → ZMod 7)) := J15_out_indep
example : (strongPowPi C7 30).IsIndepSet (J30pp_out : Set (Fin 30 → ZMod 7)) := J30pp_out_indep
example : J10_out.card = 27488 := J10_out_card
example : J10_in.card = 107265 := J10_in_card
example : J15_out.card = 12839823 := J15_out_card
example : J15_in.card = 36655232 := J15_in_card
example : J30pp_out.card = 841760069965664 := J30pp_out_card
example : J30pp_in.card = 1613966374762433 := J30pp_in_card

-- Verify key intermediate layer weights
example : R10.w .B = 129601 ∧ R10A.w .B = 129601 := ⟨R10_w.1, R10A_w.1⟩
example : R15_het.w .B = 46990439 ∧ R15_AX.w .B = 46990439 ∧ R15_Ahet.w .B = 46990439 :=
  ⟨R15_het_w.1, R15_AX_w.1, R15_Ahet_w.1⟩
example : R20_sub.w .B = 17094983041 := R20_sub_w.1
example : R30L.w .B = 2278775073866497 ∧ R30hat.w .B = 2278775073866497 := ⟨R30L_w.1, R30hat_w.1⟩
example : R35_sub.w .B = 834016390090402087 := R35_sub_w.1
example : R40_s0.w .B = 305594401588752181313 := R40_s0_w.1
example : R65_s1.w .B = 2039192944090686516848487970697063 := R65_s1_w.1
example : R50_s2.w .B = 41138135602767342342736833 := R50_s2_w.1
example : R155.w .B = 31398559828202508413609104503159115620899485238776156841255756564887950260469559 :=
  R155_w.1

-- Verify final d=620 lower bound, cardinality, strict improvements, and sharpness
example : m620Card ≤ (strongPowPi (SimpleGraph.cycleGraph 7) 620).indepNum := c7_lower_m1_card
example : c7_lower_num_m1 ^ 620 ≤ c7_lower_den_m1 ^ 620 * m620Card := c7_lower_m1_pow_le
example : (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) ≤ shannonCapacity (SimpleGraph.cycleGraph 7) :=
  c7_lower_m1
example : (c7_portfolio_num : ℝ) / (c7_portfolio_den : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) :=
  c7_lower_m1_gt_portfolio
example : (3258827985920007 : ℝ) / (1000000000000000 : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) :=
  c7_lower_m1_gt_bpz_v2
example : (3258832620353266 : ℝ) / (1000000000000000 : ℝ) < (c7_lower_num_m1 : ℝ) / (c7_lower_den_m1 : ℝ) :=
  c7_lower_m1_gt_tandon
example : c7_lower_den_m1 ^ 620 * m620Card < (c7_lower_num_m1 + 1) ^ 620 := c7_lower_m1_sharp

-- Verify axioms on core certificates and final theorems
#print axioms ShannonC7.BPZTables.T2a_ok
#print axioms ShannonC7.BPZTables.T3b_ok
#print axioms ShannonC7.BPZTables.C4a_ok
#print axioms ShannonC7.w_hetGao
#print axioms ShannonC7.J10_out_card
#print axioms ShannonC7.J15_out_card
#print axioms ShannonC7.J30pp_out_card
#print axioms ShannonC7.m620Card_le_pi
#print axioms ShannonC7.c7_lower_m1_card
#print axioms ShannonC7.c7_lower_m1_pow_le
#print axioms ShannonC7.c7_lower_m1
#print axioms ShannonC7.c7_lower_m1_gt_portfolio
#print axioms ShannonC7.c7_lower_m1_gt_bpz_v2
#print axioms ShannonC7.c7_lower_m1_gt_tandon
#print axioms ShannonC7.c7_lower_m1_sharp

end ShannonC7.Tests

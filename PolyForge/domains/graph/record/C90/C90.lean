import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C90 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    3 * (G.indepNum : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) + 11 := by
  have s1 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s3 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s6 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s7 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*alpha <= 1
          have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s12 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s13 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s12]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s15 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s8, s9, s10, s13, s14]
          linarith [s15]
      linarith [s2]
    · -- 1*omega <= 2
      have s16 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by
        by_cases hc16 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s21 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc16; omega
          have s22 : 3 * (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s21]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s24 : 5 * (G.maxDegree : ℤ) + 10 * (G.chromaticNumber.toNat : ℤ) + 15 * (G.indepNum : ℤ) ≥ 73 := by linarith [s17, s18, s19, s22, s23]
          have s25 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by have hr := s24; omega
          linarith [s25]
        · -- 1*alpha <= 2
          have s26 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s27 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s28 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s27])
            try push_cast at hw
            linarith [hw]
          have s29 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s30 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc16; omega
          have s31 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s32 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s31]) (by linarith [s29])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s26, s29, s30, s32]
          have s34 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s35 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s36 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s34, s35]
          have s37 : 14 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 40 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (10 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s36]) (by linarith [s33])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s38 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s39 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s28, s37, s38]
          have s40 : 15 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 50 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (10 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s39]) (by linarith [s33])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s41 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s42 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s30]) (by linarith [s41])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s43 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s34, s26, s30, s42, s35]
          have s44 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
              mul_nonneg (by linarith [s30]) (by linarith [s43])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s45 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s26, s30, s28, s37, s44, s38]
          have s46 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s45; omega
          have s47 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s30]) (by linarith [s46])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s48 : 9 * (G.maxDegree : ℤ) + 18 * (G.chromaticNumber.toNat : ℤ) + 27 * (G.indepNum : ℤ) ≥ 131 := by linarith [s26, s28, s40, s47, s35, s38]
          have s49 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by have hr := s48; omega
          linarith [s49]
      linarith [s16]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

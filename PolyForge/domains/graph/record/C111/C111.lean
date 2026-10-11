import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C111 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) :
    2 * (G.edgeFinset.card : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) + 11 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s6 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s7 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*chi <= 2
          have s8 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by
            by_cases hc8 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc8; omega
              have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s13 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by linarith [s9, s10, s11, s12]
              linarith [s13]
            · -- 1*chi <= 1
              have s14 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc8; omega
              have s17 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s18 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s17]) (by linarith [s16])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s20 : (G.maxDegree : ℤ) = 3 := by
                have hw := regular_max_int' G hp1
                try push_cast at hw
                linarith [hw]
              have s21 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s22 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 14 := by linarith [s14, s15, s16, s18, s19, s20, s21]
              linarith [s22]
          linarith [s8]
      linarith [s2]
    · -- 1*alpha <= 2
      have s23 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by
        by_cases hc23 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s24 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by
            by_cases hc24 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s25 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s26 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc23; omega
              have s27 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc24; omega
              have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s29 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s30 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 12 := by linarith [s25, s26, s27, s28, s29]
              linarith [s30]
            · -- 1*alpha <= 1
              have s31 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s32 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s34 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s35 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc24; omega
              have s36 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s35]) (by linarith [s34])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s38 : (G.maxDegree : ℤ) = 3 := by
                have hw := regular_max_int' G hp1
                try push_cast at hw
                linarith [hw]
              have s39 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s40 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by linarith [s31, s32, s33, s36, s37, s38, s39]
              linarith [s40]
          linarith [s24]
        · -- 1*omega <= 2
          have s41 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by
            by_cases hc41 : (4 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 4
              have s42 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hcc := hc41; omega
              have s43 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s44 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s45 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s46 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by linarith [s42, s43, s44, s45]
              linarith [s46]
            · -- 1*chi <= 3
              have s47 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s48 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s49 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hcc := hc41; omega
              have s50 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s51 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s50]) (by linarith [s49])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s52 : (G.maxDegree : ℤ) = 3 := by
                have hw := regular_max_int' G hp1
                try push_cast at hw
                linarith [hw]
              have s53 : 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s47, s48, s49, s51, s52]
              have s54 : (G.indepNum : ℤ) ≥ 2 := by have hr := s53; omega
              have s55 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc23; omega
              have s56 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s55])
                try push_cast at hw
                linarith [hw]
              have s57 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s47, s52]
              have s58 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s59 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s60 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s58]) (by linarith [s59])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s61 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s48, s58, s49, s60]
              have s62 : 10 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 24 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (6 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s57]) (by linarith [s61])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s63 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s47, s48, s58, s60, s52]
              have s64 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
                  mul_nonneg (by linarith [s58]) (by linarith [s63])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s65 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s66 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
                have hw := regular_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s67 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 12 := by linarith [s54, s48, s56, s62, s64, s65, s66]
              linarith [s67]
          linarith [s41]
      linarith [s23]
  linarith [s1]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C16 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    (G.chromaticNumber.toNat : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 5 := by
  have s1 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 3
      have s2 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
        by_cases hc2 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s3 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc2; omega
              have s6 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s7 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
              have s8 : 3 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (3 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s5]) (by linarith [s7])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s9 : 4 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 11 := by linarith [s4, s5, s6, s7, s8]
              have s10 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by have hr := s9; omega
              linarith [s10]
            · -- 1*chi <= 2
              have s11 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc2; omega
              have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s14 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s14]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s16 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s11, s12, s13, s15]
              have s17 : (G.indepNum : ℤ) ≥ 3 := by have hr := s16; omega
              have s18 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
              have s19 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s20 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
              have s21 : 3 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (3 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s11]) (by linarith [s20])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s22 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s17]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s24 : 12 * (Fintype.card V : ℤ) - 6 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) ≥ 25 := by linarith [s17, s18, s19, s12, s20, s21, s22, s23]
              have s25 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by have hr := s24; omega
              linarith [s25]
          linarith [s3]
        · -- 1*n <= 4
          have s26 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            by_cases hc26 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s27 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc26; omega
              have s29 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s30 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
              have s31 : (G.maxDegree : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s32 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc2; omega
              have s33 : 3 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
                have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 3) :=
                  mul_nonneg (by linarith [s32]) (by linarith [s31])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s34 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s27, s28, s29, s30, s33]
              linarith [s34]
            · -- 1*chi <= 2
              have s35 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
              have s36 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s37 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc2; omega
              have s38 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s39 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc26; omega
              have s40 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s38]) (by linarith [s39])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s41 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s42 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s35, s36, s37, s40, s41]
              have s43 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s44 : (G.maxDegree : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s45 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s43, s44]
              have s46 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s47 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s46]) (by linarith [s37])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s48 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s49 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s48, s39]
              have s50 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s49])
                try push_cast at hw
                linarith [hw]
              have s51 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [s42, s45, s47, s50]
              linarith [s51]
          linarith [s26]
      linarith [s2]
    · -- 1*max_deg <= 2
      have s52 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        by_cases hc52 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s53 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc52; omega
          have s54 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s55 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
          have s56 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s57 : -(G.maxDegree : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s58 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s59 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s58]) (by linarith [s57])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s60 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s61 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [s53, s54, s55, s56, s57, s59, s60]
          linarith [s61]
        · -- 1*chi <= 2
          have s62 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
          have s63 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s64 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s65 : -(G.maxDegree : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s66 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s67 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc52; omega
          have s68 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s66]) (by linarith [s67])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s69 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s70 : 2 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s69]) (by linarith [s65])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s71 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s72 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [s62, s63, s64, s65, s68, s70, s71]
          linarith [s72]
      linarith [s52]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

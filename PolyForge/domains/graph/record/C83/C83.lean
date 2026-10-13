import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C83 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 3) :
    2 * (G.minDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 5 := by
  have s1 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s6 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s7 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s8 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*chi <= 2
              have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s10 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s14 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s15 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s14]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s16 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s9, s10, s11, s12, s13, s15]
              linarith [s16]
          linarith [s3]
        · -- 1*alpha <= 2
          have s17 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s21 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s19, s20]
          have s22 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s23 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s22]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s17, s18, s22, s24]
          have s26 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s22]) (by linarith [s25])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s17, s18, s21, s26]
          linarith [s27]
      linarith [s2]
    · -- 1*n <= 5
      have s28 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
        by_cases hc28 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s29 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
            by_cases hc29 : (3 : ℤ) ≤ (G.vertexCoverNum.toNat : ℤ)
            · -- 1*tau >= 3
              have s30 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hcc := hc29; omega
              have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s32 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s33 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s34 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s32, s33]
              have s35 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s36 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s37 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
              have s38 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s36, s37]
              have s39 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s35]) (by linarith [s38])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s40 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc28; omega
              have s41 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s42 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s30, s37, s41]
              have s43 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s42]) (by linarith [s40])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s44 : -12 * (G.minDegree : ℤ) + 12 * (G.chromaticNumber.toNat : ℤ) + 18 * (G.indepNum : ℤ) ≥ 25 := by linarith [s30, s31, s34, s39, s43, s41]
              have s45 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s44; omega
              linarith [s45]
            · -- 1*tau <= 2
              have s46 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s47 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s48 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s49 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc28; omega
              have s50 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hcc := hc29; omega
              have s51 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s52 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by linarith [s46, s47, s48, s49, s50, s51]
              linarith [s52]
          linarith [s29]
        · -- 1*chi <= 2
          have s53 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s54 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s55 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s56 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s57 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc28; omega
          have s58 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s56]) (by linarith [s57])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s59 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s60 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s61 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
          have s62 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s60]) (by linarith [s61])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s63 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s64 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s63, s57]
          have s65 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s64])
            try push_cast at hw
            linarith [hw]
          have s66 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s67 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s53, s66]
          have s68 : -3 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -15 := by
            have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s61]) (by linarith [s67])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s69 : -2 * (G.minDegree : ℤ) ≥ -5 := by linarith [s59, s62, s65, s68]
          have s70 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s69; omega
          have s71 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s72 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s73 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s74 : -(G.indepNum : ℤ) ≥ -5 := by linarith [s72, s61, s73]
          have s75 : 5 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ (5 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s74]) (by linarith [s71])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s76 : -18 * (G.minDegree : ℤ) + 18 * (G.chromaticNumber.toNat : ℤ) + 27 * (G.indepNum : ℤ) ≥ 37 := by linarith [s53, s54, s55, s58, s70, s75]
          have s77 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s76; omega
          linarith [s77]
      linarith [s28]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

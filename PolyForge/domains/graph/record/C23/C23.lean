import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C23 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) :
    2 * (G.maxDegree : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) + 1 := by
  have s1 : 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s5]
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
      have s9 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s7, s2, s8]
      have s10 : 5 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s6]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s2, s8]
      have s12 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s13 : 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 6 * (G.maxDegree : ℤ) ≥ 5 := by linarith [s2, s3, s10, s13]
      have s15 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s14; omega
      have s16 : (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s11]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : 21 * (G.maxDegree : ℤ) ≥ 25 := by linarith [s2, s3, s10, s16]
      have s18 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s17; omega
      have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [s4, s2, s8]
      have s22 : (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s23 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s24 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s25 : -(G.indepNum : ℤ) ≥ -6 := by linarith [s2, s23, s8, s24]
      have s26 : 6 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 18 := by
        have hmul : (0 : ℤ) ≤ (6 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
          mul_nonneg (by linarith [s25]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s27 : 22 * (G.maxDegree : ℤ) + 33 * (G.chromaticNumber.toNat : ℤ) - 33 * (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [s18, s19, s11, s22, s26, s24]
      have s28 : 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s27; omega
      linarith [s28]
    · -- 1*chi <= 2
      have s29 : 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        by_cases hc29 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
        · -- 1*max_deg >= 2
          have s30 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc29; omega
          have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s32 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s33 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s34 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s32, s33]
          have s35 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s36 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s37 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s38 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s37]) (by linarith [s35])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s39 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s36, s30, s31, s35, s38]
          have s40 : (G.indepNum : ℤ) ≥ 2 := by have hr := s39; omega
          have s41 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s40]) (by linarith [s35])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s42 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s43 : 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s30, s31, s34, s41, s42]
          linarith [s43]
        · -- 1*max_deg <= 1
          have s44 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s45 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s46 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s47 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s48 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s49 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s50 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s51 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s49]) (by linarith [s50])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s52 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s53 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc29; omega
          have s54 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s52]) (by linarith [s53])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s55 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s56 : 2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s44, s45, s46, s47, s48, s51, s54, s55]
          linarith [s56]
      linarith [s29]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

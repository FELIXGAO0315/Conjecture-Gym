import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C104 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) :
    4 * (Fintype.card V : ℤ) ≤ -3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) + 18 := by
  have s1 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -18 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 2
      have s2 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -18 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s4 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := bipartite_four_mul_edges_int G (isAcyclic_bipartite G hp1)
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := acyclic_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s7 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s9]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s11 : (Fintype.card V : ℤ) ≥ 1 := by
            have hw := card_ge_one_int (V := V)
            try push_cast at hw
            linarith [hw]
          have s12 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s11]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -2 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s6, s7, s3, s8, s5, s10, s12, s13]
          have s15 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hr := s14; omega
          have s16 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s17 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s18 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s16, s17]
          have s19 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [s7, s3, s5, s12]
          have s20 : 8 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 15 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s18]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -3 * (G.minDegree : ℤ) ≥ -10 := by linarith [s21, s16, s3, s5, s12]
          have s23 : -(G.minDegree : ℤ) ≥ -3 := by have hr := s22; omega
          have s24 : -3 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -15 := by
            have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s23])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : -2 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ -35 := by linarith [s3, s4, s5, s15, s20, s24]
          have s26 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -17 := by have hr := s25; omega
          linarith [s26]
        · -- 1*min_deg <= 1
          have s27 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := acyclic_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s28 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp2
            try push_cast at hw
            linarith [hw]
          have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s31 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s32 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s33 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s32]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s35 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -18 := by linarith [s27, s28, s29, s30, s31, s33, s34]
          linarith [s35]
      linarith [s2]
    · -- 1*max_deg <= 1
      have s36 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s37 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s38 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s39 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s40 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s41 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s42 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s43 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s42]) (by linarith [s37])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s44 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s45 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s44]) (by linarith [s41])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s46 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s47 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -8 := by linarith [s36, s37, s38, s39, s40, s41, s43, s45, s46]
      linarith [s47]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

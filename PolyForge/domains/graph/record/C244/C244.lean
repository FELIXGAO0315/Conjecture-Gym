import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C244 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hp2 : G.Connected) (hn1 : (G.minDegree : ℤ) ≤ 4) :
    (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) - 4 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by
        by_cases hc2 : (4 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 4
          have s3 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := bipartite_chi_int G hp1
                try push_cast at hw
                linarith [hw]
              have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s7 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc2; omega
              have s8 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s7]) (by linarith [s4])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s9 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s7, s10, s11]
              have s13 : -2 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -8 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s12]) (by linarith [s9])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s14 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [s4, s5, s6, s8, s13, s11]
              linarith [s14]
            · -- 1*min_deg <= 1
              have s15 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
                have hw := connected_edges_int G hp2
                try push_cast at hw
                linarith [hw]
              have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := bipartite_chi_int G hp1
                try push_cast at hw
                linarith [hw]
              have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s18 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s19 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc2; omega
              have s20 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s16])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s22 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [s15, s16, s17, s18, s20, s21]
              linarith [s22]
          linarith [s3]
        · -- 1*alpha <= 3
          have s23 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s24 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
            have hw := connected_edges_int G hp2
            try push_cast at hw
            linarith [hw]
          have s25 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := bipartite_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s28 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s30 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s28]) (by linarith [s29])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s31 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s26, s27, s28, s30]
          have s32 : -(G.minDegree : ℤ) ≥ -4 := by linarith [hn1]
          have s33 : -4 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -24 := by
            have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s31]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s35 : 3 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ -13 := by linarith [s23, s24, s25, s31, s33, s34]
          have s36 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by have hr := s35; omega
          linarith [s36]
      linarith [s2]
    · -- 1*alpha <= 2
      have s37 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s38 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s39 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s40 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s41 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s42 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s43 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s42]) (by linarith [s39])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s44 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s45 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s46 : (G.edgeFinset.card : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s44, s39, s41, s43, s45]
      have s47 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s48 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s39, s41, s47, s43]
      have s49 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s50 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s47]) (by linarith [s49])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s51 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s37, s38, s39, s41, s47, s50]
      have s52 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s48]) (by linarith [s51])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s53 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) - 10 * (G.vertexCoverNum.toNat : ℤ) ≥ -23 := by linarith [s37, s38, s39, s40, s41, s43, s46, s52, s45]
      have s54 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by have hr := s53; omega
      linarith [s54]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

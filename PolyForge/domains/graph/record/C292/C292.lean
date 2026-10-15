import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C292 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) :
    (G.edgeFinset.card : ℤ) ≤ -2 * (Fintype.card V : ℤ) + 5 * (G.indepNum : ℤ) + 2 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 2
      have s2 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.vertexCoverNum.toNat : ℤ)
        · -- 1*tau >= 2
          have s3 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by
            by_cases hc3 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 5
              have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := acyclic_chi_int G hp1
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc3; omega
              have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s7 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
              have s8 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s9 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s4])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -2 * (G.edgeFinset.card : ℤ) + 6 * (G.indepNum : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s4, s5, s6, s7, s9, s10]
              have s12 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hr := s11; omega
              linarith [s12]
            · -- 1*n <= 4
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
                have hw := acyclic_chi_int G hp1
                try push_cast at hw
                linarith [hw]
              have s14 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := bipartite_four_mul_edges_int G (isAcyclic_bipartite G hp1)
                try push_cast at hw
                linarith [hw]
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s16 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc3; omega
              have s17 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s18 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s17]) (by linarith [s16])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s19 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s20 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s22 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [s13, s14, s15, s16, s18, s20, s21]
              linarith [s22]
          linarith [s3]
        · -- 1*tau <= 1
          have s23 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
          have s26 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s27 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s29 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s27, s28]
          have s30 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s30, s25]
          have s32 : 5 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 10 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (5 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s29]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s34 : -7 * (G.edgeFinset.card : ℤ) + 21 * (G.indepNum : ℤ) - 14 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [s23, s24, s25, s26, s32, s33]
          have s35 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by have hr := s34; omega
          linarith [s35]
      linarith [s2]
    · -- 1*chi <= 1
      have s36 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s37 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s38 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s39 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s40 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s41 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s40]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s42 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s43 : -(G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [s38, s39, s41, s42]
      have s44 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s45 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s46 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
      have s47 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s45, s46]
      have s48 : 5 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s44]) (by linarith [s47])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s49 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s36, s37, s43, s48, s42]
      linarith [s49]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

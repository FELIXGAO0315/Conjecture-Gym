import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C79 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by
    by_cases hc1 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 4
      have s2 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by
        by_cases hc2 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s4 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := bipartite_four_mul_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s6 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc2; omega
          have s7 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s6]) (by linarith [s5])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
            have hw := bipartite_chi_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
          have s12 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s8, s9, s10, s11, s13]
          have s15 : 13 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 40 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (8 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s6]) (by linarith [s14])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.minDegree : ℤ) ≥ -7 := by linarith [s8, s16, s17, s9, s10, s11, s13]
          have s19 : -7 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -56 := by
            have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (7 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s14]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : -109 * (G.minDegree : ℤ) ≥ -448 := by linarith [s3, s4, s7, s15, s19]
          have s21 : -(G.minDegree : ℤ) ≥ -4 := by have hr := s20; omega
          have s22 : -4 * (Fintype.card V : ℤ) - 8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -32 := by
            have hmul : (0 : ℤ) ≤ (8 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s14]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : 79 * (G.edgeFinset.card : ℤ) - 237 * (G.minDegree : ℤ) ≥ -128 := by linarith [s3, s4, s7, s15, s22]
          have s24 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -1 := by have hr := s23; omega
          linarith [s24]
        · -- 1*n <= 4
          have s25 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s26 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := bipartite_four_mul_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s27 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc2; omega
          have s28 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc2; omega
          have s29 : 8 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 16 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (4 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s28]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s30 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s31 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s28]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by linarith [s25, s26, s27, s29, s31]
          linarith [s32]
      linarith [s2]
    · -- 1*n <= 3
      have s33 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s34 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s35 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s36 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := bipartite_four_mul_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s37 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s38 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s39 : 4 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 3 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s37]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s40 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s33, s34, s38]
      have s41 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s38]) (by linarith [s40])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s42 : 4 * (G.edgeFinset.card : ℤ) - 12 * (G.minDegree : ℤ) ≥ -11 := by linarith [s33, s34, s35, s36, s39, s41]
      have s43 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by have hr := s42; omega
      linarith [s43]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

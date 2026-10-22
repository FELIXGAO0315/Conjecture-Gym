import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C223 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 6) :
    2 * (G.cliqueNum : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by
    by_cases hc1 : (8 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 8
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 6 := by
        by_cases hc2 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 7
          have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
          have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s8 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc2; omega
          have s9 : -7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s8]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s10 : 21 * (G.edgeFinset.card : ℤ) - 14 * (G.minDegree : ℤ) - 14 * (G.cliqueNum : ℤ) ≥ 38 := by linarith [s3, s4, s5, s6, s9]
          have s11 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 6 := by have hr := s10; omega
          linarith [s11]
        · -- 1*n <= 6
          have s12 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s14 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc2; omega
          have s18 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [s15, s16, s17]
          have s19 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s20 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s21 : -(G.minDegree : ℤ) ≥ -5 := by linarith [s19, s20, s17]
          have s22 : -5 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -30 := by
            have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (5 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s17]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ 20 := by linarith [s12, s13, s14, s18, s22]
          have s24 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 7 := by have hr := s23; omega
          linarith [s24]
      linarith [s2]
    · -- 1*m <= 7
      have s25 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by
        by_cases hc25 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s26 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s27 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s28 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s30 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc25; omega
          have s31 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s30]) (by linarith [s29])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -2 := by linarith [s26, s27, s28, s31]
          linarith [s32]
        · -- 1*n <= 3
          have s33 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s34 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s35 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s36 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s37 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s38 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc25; omega
          have s39 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s40 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s33, s39, s38]
          have s41 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s38]) (by linarith [s40])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s42 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ -10 := by linarith [s33, s34, s35, s36, s37, s41]
          have s43 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by have hr := s42; omega
          linarith [s43]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

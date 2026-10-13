import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C85 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 6) (hn2 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) + 1 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
    by_cases hc1 : (8 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 8
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 8 := by
        by_cases hc2 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 7
          have s3 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
          have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s7 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc2; omega
          have s8 : -7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s7]) (by linarith [s6])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : 21 * (G.edgeFinset.card : ℤ) - 14 * (G.maxDegree : ℤ) - 14 * (G.minDegree : ℤ) ≥ 52 := by linarith [s3, s4, s5, s8]
          have s10 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 8 := by have hr := s9; omega
          linarith [s10]
        · -- 1*n <= 6
          have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hcc := hc1; omega
          have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc2; omega
          have s15 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s11, s14]
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(G.minDegree : ℤ) ≥ -5 := by linarith [s16, s11, s14]
          have s18 : -5 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -30 := by
            have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (5 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s14]) (by linarith [s17])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s19 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ 26 := by linarith [s11, s12, s13, s15, s18]
          have s20 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 9 := by have hr := s19; omega
          linarith [s20]
      linarith [s2]
    · -- 1*m <= 7
      have s21 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by
        by_cases hc21 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s22 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s23 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s24 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s25 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc21; omega
          have s26 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s25]) (by linarith [s24])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s22, s23, s26]
          linarith [s27]
        · -- 1*n <= 3
          have s28 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s30 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s31 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s32 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc21; omega
          have s33 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s28, s29, s32]
          have s34 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
            have hmul : (0 : ℤ) ≤ (3 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s32]) (by linarith [s33])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s35 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ -4 := by linarith [s28, s29, s30, s31, s34]
          have s36 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by have hr := s35; omega
          linarith [s36]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

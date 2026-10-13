import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C67 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 6) (hn2 : (G.cliqueNum : ℤ) ≥ 6) :
    (G.maxDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 5 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ -5 := by
    by_cases hc1 : (21 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 21
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.edgeFinset.card : ℤ) ≥ 21 := by have hcc := hc1; omega
      have s4 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
      have s5 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ -3 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*m <= 20
      have s6 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ -5 := by
        by_cases hc6 : (8 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 8
          have s7 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
          have s10 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s11 : (Fintype.card V : ℤ) ≥ 8 := by have hcc := hc6; omega
          have s12 : -8 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 8) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s11]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ -9 := by linarith [s7, s8, s9, s12]
          have s14 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ -4 := by have hr := s13; omega
          linarith [s14]
        · -- 1*n <= 7
          have s15 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s16 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s17 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s19 : (G.cliqueNum : ℤ) ≥ 6 := by linarith [hn2]
          have s20 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s21 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s19, s20]
          have s22 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s21]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : -(Fintype.card V : ℤ) ≥ -7 := by have hcc := hc6; omega
          have s24 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
          have s26 : -(G.minDegree : ℤ) ≥ -6 := by linarith [s24, s25]
          have s27 : -6 * (Fintype.card V : ℤ) - 7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -42 := by
            have hmul : (0 : ℤ) ≤ (7 - (Fintype.card V : ℤ)) * (6 - (G.minDegree : ℤ)) :=
              mul_nonneg (by linarith [s23]) (by linarith [s26])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : 19 * (G.edgeFinset.card : ℤ) - 19 * (G.maxDegree : ℤ) - 57 * (G.minDegree : ℤ) ≥ -108 := by linarith [s15, s16, s17, s22, s27]
          have s29 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ -5 := by have hr := s28; omega
          linarith [s29]
      linarith [s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C55 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 6) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 16 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by
    by_cases hc1 : (5 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 5
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
        · -- 1*max_deg >= 2
          have s3 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.minDegree : ℤ)
            · -- 1*min_deg >= 2
              have s4 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s5 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
              have s6 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s7 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s8 : -2 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 2) :=
                  mul_nonneg (by linarith [s5]) (by linarith [s6])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s9 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by linarith [s4, s5, s6, s7, s8]
              linarith [s9]
            · -- 1*min_deg <= 1
              have s10 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s11 : (G.edgeFinset.card : ℤ) ≥ 5 := by have hcc := hc1; omega
              have s12 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s13 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by linarith [s10, s11, s12]
              linarith [s13]
          linarith [s3]
        · -- 1*max_deg <= 1
          have s14 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s16 : (G.edgeFinset.card : ℤ) ≥ 5 := by have hcc := hc1; omega
          have s17 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s19 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
          have s20 : (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * (1 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s22 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 28 := by linarith [s14, s15, s16, s17, s18, s20, s21]
          linarith [s22]
      linarith [s2]
    · -- 1*m <= 4
      have s23 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
      have s24 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s25 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s26 : -(G.edgeFinset.card : ℤ) ≥ -4 := by have hcc := hc1; omega
      have s27 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s28 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s23]) (by linarith [s27])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s30 : 9 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 9 * (G.indepNum : ℤ) ≥ 46 := by linarith [s23, s24, s25, s26, s28, s29]
      have s31 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by have hr := s30; omega
      linarith [s31]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

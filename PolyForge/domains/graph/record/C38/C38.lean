import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C38 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≥ 4) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 10 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 2
      have s2 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.minDegree : ℤ)
        · -- 1*min_deg >= 2
          have s3 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s4 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
          have s5 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s7 : -2 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -8 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 2) :=
              mul_nonneg (by linarith [s4]) (by linarith [s5])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s8 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s3, s4, s5, s6, s7]
          linarith [s8]
        · -- 1*min_deg <= 1
          have s9 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
          have s10 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s13 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s9, s10, s11, s12]
          linarith [s13]
      linarith [s2]
    · -- 1*max_deg <= 1
      have s14 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
      have s15 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s16 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s19 : (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s21 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s14]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s23 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s14, s15, s16, s17, s18, s19, s21, s22]
      linarith [s23]
  linarith [s1]

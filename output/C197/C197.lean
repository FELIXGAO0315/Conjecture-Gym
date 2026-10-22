import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C197 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) :
    (G.maxDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 1 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 2
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s8 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s9 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s7]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s11 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by linarith [s2, s3, s4, s5, s6, s9, s10]
      linarith [s11]
    · -- 1*min_deg <= 1
      have s12 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
      have s15 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s16 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by linarith [s12, s13, s14, s15]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

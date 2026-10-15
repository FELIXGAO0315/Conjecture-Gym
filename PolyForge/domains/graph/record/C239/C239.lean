import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C239 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 5) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 1
      have s2 : (G.indepNum : ℤ) ≥ 5 := by linarith [hn1]
      have s3 : (G.minDegree : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn2]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s6]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s9 : 2 * (G.edgeFinset.card : ℤ) ≥ 7 := by linarith [s2, s3, s4, s5, s7, s8]
      have s10 : (G.edgeFinset.card : ℤ) ≥ 4 := by have hr := s9; omega
      have s11 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s2, s4, s8]
      have s12 : -(Fintype.card V : ℤ) - 7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -7 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s11]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 7 * (G.edgeFinset.card : ℤ) - 14 * (G.minDegree : ℤ) ≥ 12 := by linarith [s2, s10, s4, s5, s12, s8]
      have s14 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by have hr := s13; omega
      linarith [s14]
    · -- 1*min_deg <= 0
      have s15 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn2]
      have s17 : -(G.minDegree : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s18 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 2 := by linarith [s15, s16, s17]
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C97 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 5) (hn2 : (G.cliqueNum : ℤ) ≥ 2) :
    (G.maxDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 1
      have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.indepNum : ℤ) ≥ 5 := by linarith [hn1]
      have s4 : (G.minDegree : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s7]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s10 : 2 * (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [s3, s4, s5, s6, s8, s9]
      have s11 : (G.edgeFinset.card : ℤ) ≥ 3 := by have hr := s10; omega
      have s12 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s3, s5, s9]
      have s13 : -(Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -5 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s12]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 15 * (G.edgeFinset.card : ℤ) - 5 * (G.maxDegree : ℤ) - 15 * (G.minDegree : ℤ) ≥ 12 := by linarith [s2, s3, s11, s5, s6, s13, s9]
      have s15 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 3 := by have hr := s14; omega
      linarith [s15]
    · -- 1*min_deg <= 0
      have s16 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.cliqueNum : ℤ) ≥ 2 := by linarith [hn2]
      have s18 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.minDegree : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s20 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by linarith [s16, s17, s18, s19]
      linarith [s20]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

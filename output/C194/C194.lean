import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C194 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 5) :
    2 * (G.maxDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 2
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) ≥ 5 := by linarith [hn1]
      have s4 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s7 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s6]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5, s7]
      have s9 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s2, s3]
      have s10 : -2 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s9]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by linarith [s2, s8, s5, s7, s10]
      linarith [s11]
    · -- 1*min_deg <= 1
      have s12 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.maxDegree : ℤ) ≥ 5 := by linarith [hn1]
      have s14 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s15 : 3 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by linarith [s12, s13, s14]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

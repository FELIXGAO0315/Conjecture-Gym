import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C166 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 2) :
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
      have s4 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn1]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s7 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s8 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s6]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by linarith [s2, s3, s4, s5, s8]
      linarith [s9]
    · -- 1*min_deg <= 1
      have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn1]
      have s12 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s13 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by linarith [s10, s11, s12]
      linarith [s13]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

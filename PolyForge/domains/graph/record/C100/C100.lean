import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C100 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 3) (hn2 : (G.minDegree : ℤ) ≥ 1) :
    (G.maxDegree : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 1 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by
    by_cases hc1 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 4
      have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s4 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.minDegree : ℤ) ≥ 1 := by linarith [hn2]
      have s7 : -(Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s3]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : 6 * (G.edgeFinset.card : ℤ) - 2 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s7]
      have s9 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 2 := by have hr := s8; omega
      linarith [s9]
    · -- 1*n <= 3
      have s10 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
      have s13 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s14 : 3 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) ≥ 1 := by linarith [s10, s11, s12, s13]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

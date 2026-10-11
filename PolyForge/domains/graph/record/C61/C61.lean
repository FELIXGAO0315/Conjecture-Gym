import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C61 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    (G.maxDegree : ℤ) ≥ (G.edgeFinset.card : ℤ) - 3 * (G.indepNum : ℤ) + 3 := by
  have s1 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 2
      have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s4 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
      have s5 : (Fintype.card V : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s6 : 3 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (3 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s5]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s6, s7]
      linarith [s8]
    · -- 1*n <= 1
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s11 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := two_mul_edges_le_card_sq_sub_card_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s13 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s14 : 2 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s9, s10, s11, s12, s14]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

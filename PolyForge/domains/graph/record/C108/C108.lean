import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C108 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.minDegree : ℤ)) :
    (G.indepNum : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s4, s5, s3]
  have s7 : (G.minDegree : ℤ) ≥ 1 := by linarith [s4, s5, s3]
  have s8 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s6]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : 3 * (G.edgeFinset.card : ℤ) - (G.indepNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s1, s2, s3, s8, s9]
  linarith [s10]

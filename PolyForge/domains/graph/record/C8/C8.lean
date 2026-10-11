import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C8 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ (G.indepNum : ℤ)) :
    2 * (Fintype.card V : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) + 1 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : (G.minDegree : ℤ) ≥ 1 := by linarith [s2, s3]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s6, s7, s2, s3]
  have s9 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s8]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s11 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) ≥ -1 := by linarith [s1, s4, s5, s3, s9, s10]
  linarith [s11]

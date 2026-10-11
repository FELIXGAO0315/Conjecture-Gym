import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C109 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.minDegree : ℤ)) :
    (G.vertexCoverNum.toNat : ℤ) ≤ (G.edgeFinset.card : ℤ) - (G.indepNum : ℤ) + 1 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s3, s4, s2]
  have s6 : (G.minDegree : ℤ) ≥ 1 := by linarith [s3, s4, s2]
  have s7 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s9 : (G.edgeFinset.card : ℤ) - (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s1, s2, s7, s8]
  linarith [s9]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C68 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 4) :
    2 * (G.vertexCoverNum.toNat : ℤ) ≤ 3 * (G.maxDegree : ℤ) + 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [hn1]
  have s5 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s6 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 6 * (G.maxDegree : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [s1, s2, s3, s4, s6]
  have s8 : 3 * (G.maxDegree : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ -1 := by have hr := s7; omega
  linarith [s8]

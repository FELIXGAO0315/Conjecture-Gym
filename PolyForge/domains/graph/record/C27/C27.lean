import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C27 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 6) :
    (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 5 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 6 := by linarith [hn2]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s5 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s5, s2]
  have s7 : -7 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 7) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s6]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 7 * (G.edgeFinset.card : ℤ) - 7 * (G.minDegree : ℤ) ≥ 30 := by linarith [s1, s2, s3, s7]
  have s9 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) ≥ 5 := by have hr := s8; omega
  linarith [s9]

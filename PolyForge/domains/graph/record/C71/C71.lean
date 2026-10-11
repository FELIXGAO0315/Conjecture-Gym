import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C71 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 2 * (G.maxDegree : ℤ)) (hn2 : (G.maxDegree : ℤ) ≥ 3) :
    2 * (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) + 5 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 3 := by linarith [hn2]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s5 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s5, s2]
  have s7 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s6]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 9 := by linarith [s1, s2, s3, s7]
  have s9 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) ≥ 5 := by have hr := s8; omega
  linarith [s9]

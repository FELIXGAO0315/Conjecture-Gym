import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C53 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) (hn2 : (Fintype.card V : ℤ) ≤ 4) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + 1 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [hn2]
  have s6 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s1, s2, s5]
  have s7 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
    have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) ≥ -9 := by linarith [s1, s2, s3, s4, s7]
  have s9 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ -1 := by have hr := s8; omega
  linarith [s9]

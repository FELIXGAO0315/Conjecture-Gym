import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C81 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 6) :
    (G.maxDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s5 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn1]
  have s6 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s5]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s2, s3, s6]
  linarith [s7]

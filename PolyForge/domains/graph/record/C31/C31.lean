import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C31 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hn1 : (G.edgeFinset.card : ℤ) ≥ 6) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    (G.edgeFinset.card : ℤ) ≤ 10 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn2]
  have s4 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s5 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(G.edgeFinset.card : ℤ) ≥ -10 := by linarith [s1, s2, s3, s5]
  linarith [s6]

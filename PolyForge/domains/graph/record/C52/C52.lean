import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C52 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsEdgeConnected 2) (hn1 : (Fintype.card V : ℤ) ≥ 5) :
    (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 5 := by
  have s1 : (G.minDegree : ℤ) ≥ 2 := by
    have hw := edge_conn_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -2 * (Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -10 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 2) :=
      mul_nonneg (by linarith [s2]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : -(Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) ≥ 5 := by linarith [s1, s2, s3, s4]
  linarith [s5]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C32 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 1) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.indepNum : ℤ) ≤ 6) :
    (Fintype.card V : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 1 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := edge_conn_min_deg_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : -(Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -1 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s5]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s6]
  linarith [s7]

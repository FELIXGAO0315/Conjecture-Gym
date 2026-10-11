import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C24 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.IsEdgeConnected 1) (hn1 : (G.minDegree : ℤ) ≤ 2 * (G.girth : ℤ)) (hn2 : (G.girth : ℤ) ≤ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := edge_conn_min_deg_int G hp2 (hasCycle_two_le_card G hp1)
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s1, s2, s4]
  have s7 : -(Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s6]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s2, s3, s4, s7]
  linarith [s8]

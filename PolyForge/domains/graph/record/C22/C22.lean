import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C22 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsEdgeConnected 2) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.minDegree : ℤ)) (hn2 : (Fintype.card V : ℤ) ≥ 3) :
    (G.maxDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 4 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 2 := by
    have hw := edge_conn_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn2]
  have s6 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
      mul_nonneg (by linarith [s5]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 4 := by linarith [s1, s2, s3, s4, s6]
  linarith [s7]

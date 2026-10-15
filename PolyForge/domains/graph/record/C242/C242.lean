import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C242 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hp2 : 2 ≤ Fintype.card V) (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.chromaticNumber.toNat : ℤ) := by
  have s1 : (G.minDegree : ℤ) ≥ 3 := by
    have hw := edge_conn_min_deg_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -3 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s4]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.edgeFinset.card : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s1, s2, s3, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

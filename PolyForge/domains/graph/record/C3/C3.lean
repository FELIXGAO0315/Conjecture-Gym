import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C3 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsEdgeConnected 2) (hn1 : (G.cliqueNum : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 2 := by
    have hw := edge_conn_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
      mul_nonneg (by linarith [s4]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s1, s2, s3, s5]
  linarith [s6]

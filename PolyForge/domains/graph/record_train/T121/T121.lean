import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T121 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 3) (hp2 : ¬ G.IsAcyclic) :
    2 * (G.minDegree : ℤ) ≥ -3 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 16 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.minDegree : ℤ) ≥ 3 := by
    have hw := edge_conn_min_deg_int G hp1 (hasCycle_two_le_card G hp2)
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp2
    try push_cast at hw
    linarith [hw]
  have s7 : -3 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -9 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s6]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 3 * (G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 16 := by linarith [s1, s2, s3, s4, s5, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]

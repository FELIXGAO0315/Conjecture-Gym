import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C43 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.cliqueNum : ℤ) ≤ (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ 0 := by
    have hw := conn_cycle_edges_ge_card_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 3 := by
    have hw := three_le_edges_int G hp2
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 (hasCycle_two_le_card G hp2)
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp2
    try push_cast at hw
    linarith [hw]
  have s8 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s7]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -1 := by linarith [s1, s2, s3, s4, s5, s8]
  have s10 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]

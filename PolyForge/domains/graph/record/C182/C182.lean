import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C182 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.diam : ℤ) ≥ 2) :
    (G.diam : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G hp2
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.diam : ℤ) ≥ 2 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
    have hw := connected_edges_int G hp2
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - (G.diam : ℤ) ≥ 2 := by linarith [s3, s4, s1]
  have s6 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s1]
  have s8 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s7]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 3 * (G.diam : ℤ) ≥ -2 := by linarith [s1, s2, s5, s8]
  have s10 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.diam : ℤ) ≥ 0 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]

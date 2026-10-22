import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T199 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    2 * (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) - 3 * (G.girth : ℤ) + 11 := by
  have s1 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 3 := by
    have hw := three_le_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.girth : ℤ) ≥ 11 := by linarith [s1, s2, s3, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

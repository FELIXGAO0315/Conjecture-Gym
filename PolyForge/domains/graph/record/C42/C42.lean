import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C42 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    2 * (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s2]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]

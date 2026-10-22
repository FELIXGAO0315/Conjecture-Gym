import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C212 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ (G.minDegree : ℤ)) (hn2 : (G.minDegree : ℤ) ≤ 4) :
    (G.minDegree : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 4 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.minDegree : ℤ) ≥ -4 := by linarith [hn2]
  have s4 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [s2, s3]
  have s6 : 4 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) ≥ 4 := by linarith [s1, s2, s3, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

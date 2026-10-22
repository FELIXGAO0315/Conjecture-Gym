import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T311 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ -3 * (Fintype.card V : ℤ) + 2 * (G.minDegree : ℤ) + 8 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s3]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 3 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 8 := by linarith [s1, s2, s3, s4, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

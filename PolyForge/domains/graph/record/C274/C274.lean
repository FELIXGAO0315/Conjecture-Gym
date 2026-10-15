import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C274 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 2 * (Fintype.card V : ℤ)) (hn2 : (G.minDegree : ℤ) ≥ 3) :
    (G.maxDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : (G.minDegree : ℤ) ≥ 3 := by linarith [hn2]
  have s6 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s1, s2, s5]
  have s7 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s6]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ -7 := by linarith [s1, s2, s3, s4, s7]
  have s9 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ -2 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]

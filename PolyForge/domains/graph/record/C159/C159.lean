import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C159 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    2 * (G.maxDegree : ℤ) ≥ (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := two_mul_edges_le_card_sq_sub_card_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s7 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s3]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) ≥ -2 := by linarith [s1, s2, s3, s5, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]

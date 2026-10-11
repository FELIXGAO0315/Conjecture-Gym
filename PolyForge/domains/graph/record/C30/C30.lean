import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C30 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 4) :
    (G.maxDegree : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
  have s5 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) ≥ 2 := by linarith [s1, s2, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

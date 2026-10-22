import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T262 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 6) :
    (G.maxDegree : ℤ) ≤ 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 6 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : 6 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ -6 := by linarith [s1, s2, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]

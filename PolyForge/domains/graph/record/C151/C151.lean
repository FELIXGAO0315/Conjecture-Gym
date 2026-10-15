import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C151 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 5) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≤ 5) :
    2 * (G.indepNum : ℤ) ≥ -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) - 10 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
  have s3 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn2]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : 5 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) ≥ -10 := by linarith [s1, s2, s3, s5, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

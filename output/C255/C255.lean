import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C255 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 3) (hn2 : (G.indepNum : ℤ) ≥ 4) :
    2 * (G.maxDegree : ℤ) ≥ -2 * (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) + 8 := by
  have s1 : (G.indepNum : ℤ) ≥ 4 := by linarith [hn2]
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s1, s2, s5]
  have s7 : 3 * (Fintype.card V : ℤ) + 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (3 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 2 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 8 := by linarith [s1, s2, s3, s7, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]

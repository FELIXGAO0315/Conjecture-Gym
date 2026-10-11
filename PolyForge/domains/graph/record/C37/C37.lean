import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C37 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 3) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ (G.edgeFinset.card : ℤ)) :
    2 * (Fintype.card V : ℤ) ≥ 3 * (G.minDegree : ℤ) + 6 := by
  have s1 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn1]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.edgeFinset.card : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s5, s6]
  have s8 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s7]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : 2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) ≥ 6 := by linarith [s1, s2, s3, s8, s6]
  linarith [s9]

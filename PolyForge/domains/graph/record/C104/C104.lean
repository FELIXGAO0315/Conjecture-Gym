import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C104 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) - (G.indepNum : ℤ) - 1 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : 3 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) ≥ -1 := by linarith [s1, s2, s3, s4, s6, s7]
  linarith [s8]

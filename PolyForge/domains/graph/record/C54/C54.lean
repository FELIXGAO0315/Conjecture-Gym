import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 3 * (G.maxDegree : ℤ) := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
    have hw := connected_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s6 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s5]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : 3 * (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [s1, s2, s3, s4, s6, s7]
  linarith [s8]

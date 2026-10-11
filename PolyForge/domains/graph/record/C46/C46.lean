import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C46 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.indepNum : ℤ) ≥ 3) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    (Fintype.card V : ℤ) ≤ 2 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn1]
  have s2 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn2]
  have s5 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s6 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : -5 * (Fintype.card V : ℤ) + 10 * (G.maxDegree : ℤ) + 15 * (G.indepNum : ℤ) ≥ 28 := by linarith [s1, s2, s3, s4, s6, s7]
  have s9 : -(Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by have hr := s8; omega
  linarith [s9]

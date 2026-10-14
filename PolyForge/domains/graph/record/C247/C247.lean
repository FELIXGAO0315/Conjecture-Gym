import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C247 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) (hn2 : (Fintype.card V : ℤ) ≥ 5) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) - 4 := by
  have s1 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn2]
  have s2 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s1, s2]
  have s4 : (G.indepNum : ℤ) ≥ 3 := by have hr := s3; omega
  have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s1]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : 5 * (G.edgeFinset.card : ℤ) - 10 * (G.minDegree : ℤ) + 5 * (G.indepNum : ℤ) ≥ 17 := by linarith [s4, s1, s5, s6, s8, s9]
  have s11 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s10; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]

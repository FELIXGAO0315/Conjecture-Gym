import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C158 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.indepNum : ℤ) ≥ -2 * (G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) + 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
  have s3 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s6 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s2]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s1, s2, s3, s4, s6, s7]
  have s9 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 3 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T180 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 2 * (G.minDegree : ℤ) + 1 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s5, s7]
  have s9 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s8]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 3 * (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) - 6 * (G.minDegree : ℤ) ≥ 2 := by linarith [s1, s2, s3, s4, s5, s9]
  have s11 : (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 1 := by have hr := s10; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C241 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 4) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) ≥ 4 := by linarith [hn1]
  have s4 : -2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by linarith [s2, s3, s4, s5]
  have s7 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by have hr := s6; omega
  have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s10 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s2, s3]
  have s11 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s10]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s12 : 2 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s7, s8, s4, s11, s5]
  have s13 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s12; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s13, heq_gallai]

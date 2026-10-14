import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C133 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 5) (hn2 : (G.edgeFinset.card : ℤ) ≥ 6) :
    (Fintype.card V : ℤ) ≥ 4 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn2]
  have s3 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [hn1]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : 5 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s1, s2, s3, s6]
  have s8 : 5 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 15 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s7]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s10 : 4 * (G.indepNum : ℤ) + 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s1, s2, s3, s8, s9]
  have s11 : (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by have hr := s10; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]

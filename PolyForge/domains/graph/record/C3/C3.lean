import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C3 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) (hn2 : (Fintype.card V : ℤ) ≤ 5) :
    (G.vertexCoverNum.toNat : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - 26 := by
  have s1 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := two_mul_edges_le_card_sq_sub_card_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn2]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : -9 * (G.edgeFinset.card : ℤ) + 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -80 := by linarith [s1, s2, s3, s5, s6]
  have s8 : -3 * (G.edgeFinset.card : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ -26 := by have hr := s7; omega
  linarith [s8]

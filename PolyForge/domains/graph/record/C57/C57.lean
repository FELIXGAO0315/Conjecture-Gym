import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C57 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 3) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.edgeFinset.card : ℤ) ≥ -3 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [s5, s3]
  have s7 : 3 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (3 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 2 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ -1 := by linarith [s1, s2, s3, s7]
  have s9 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0 := by have hr := s8; omega
  linarith [s9]

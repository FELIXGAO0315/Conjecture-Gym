import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C50 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) (hn2 : (G.cliqueNum : ℤ) ≥ 2) :
    (G.edgeFinset.card : ℤ) ≤ (Fintype.card V : ℤ) + 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
  have s4 : (G.cliqueNum : ℤ) ≥ 2 := by linarith [hn2]
  have s5 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_card_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s4, s5]
  have s7 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s8 : -(G.maxDegree : ℤ) ≥ -5 := by linarith [s7, s3]
  have s9 : 5 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 10 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (5 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : 14 * (Fintype.card V : ℤ) - 14 * (G.edgeFinset.card : ℤ) ≥ -26 := by linarith [s1, s2, s3, s9]
  have s11 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ -1 := by have hr := s10; omega
  linarith [s11]

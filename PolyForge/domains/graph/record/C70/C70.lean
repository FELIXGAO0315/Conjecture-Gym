import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C70 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 5) (hn2 : (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ)) :
    (G.minDegree : ℤ) ≤ 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.edgeFinset.card : ℤ) ≥ -5 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn2]
  have s6 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s4, s5]
  have s7 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s8 : -(G.minDegree : ℤ) ≥ -5 := by linarith [s1, s7, s4]
  have s9 : -5 * (Fintype.card V : ℤ) - 10 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -50 := by
    have hmul : (0 : ℤ) ≤ (10 - (Fintype.card V : ℤ)) * (5 - (G.minDegree : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -3 * (G.minDegree : ℤ) ≥ -11 := by linarith [s1, s2, s3, s4, s9]
  have s11 : -(G.minDegree : ℤ) ≥ -3 := by have hr := s10; omega
  have s12 : -3 * (Fintype.card V : ℤ) - 10 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -30 := by
    have hmul : (0 : ℤ) ≤ (10 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s11])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s13 : -13 * (G.minDegree : ℤ) ≥ -37 := by linarith [s1, s2, s3, s4, s12]
  have s14 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s13; omega
  linarith [s14]

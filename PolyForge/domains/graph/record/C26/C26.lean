import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C26 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.edgeFinset.card : ℤ) ≥ 2) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2) :
    (G.minDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
  have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.minDegree : ℤ) ≥ 1 := by
    have hw := connected_min_deg_int G hp1 hp2
    try push_cast at hw
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s1, s2, s5]
  have s7 : -(Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s6]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : 6 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 7 := by linarith [s1, s2, s3, s4, s7]
  have s9 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) ≥ 3 := by have hr := s8; omega
  linarith [s9]

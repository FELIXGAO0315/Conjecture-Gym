import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C15 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 5) :
    (Fintype.card V : ℤ) ≥ -(G.edgeFinset.card : ℤ) + 3 * (G.minDegree : ℤ) + 3 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [hn1]
  have s5 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s3, s4]
  have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s5]) (by linarith [s7])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : (Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 3 := by linarith [s1, s2, s5, s6, s8]
  linarith [s9]

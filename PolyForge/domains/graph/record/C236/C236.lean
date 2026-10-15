import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C236 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 5) (hn2 : (G.minDegree : ℤ) ≥ 1) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - 2 := by
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
  have s4 : (G.minDegree : ℤ) ≥ 1 := by linarith [hn2]
  have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s5, s6]
  have s8 : -(Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 1) :=
      mul_nonneg (by linarith [s7]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by linarith [s1, s2, s3, s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s9, heq_gallai]

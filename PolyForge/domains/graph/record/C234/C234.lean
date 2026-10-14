import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C234 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ 2) :
    (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) - 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.minDegree : ℤ) ≥ 2 := by linarith [hn1]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
      mul_nonneg (by linarith [s4]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s1, s3, s2, s5]
  have s7 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s9 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s7, s8, s3]
  have s10 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
      mul_nonneg (by linarith [s9]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [s1, s2, s6, s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]

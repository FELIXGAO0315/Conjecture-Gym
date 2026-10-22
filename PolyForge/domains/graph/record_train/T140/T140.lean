import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T140 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) - 4 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s6 : (G.minDegree : ℤ) ≥ 3 := by linarith [hn1]
  have s7 : -3 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s3, s4, s2, s7]
  have s9 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s3, s4, s6]
  have s10 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 3) :=
      mul_nonneg (by linarith [s9]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [s1, s2, s8, s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s11, heq_gallai]

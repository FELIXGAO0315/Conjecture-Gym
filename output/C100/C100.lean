import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C100 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ 6) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.chromaticNumber.toNat : ℤ) := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 6 := by linarith [hn1]
  have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -6 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 6) :=
      mul_nonneg (by linarith [s4]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.edgeFinset.card : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s1, s2, s3, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

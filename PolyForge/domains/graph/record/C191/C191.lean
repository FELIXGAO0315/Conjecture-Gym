import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C191 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 4) (hn2 : (G.chromaticNumber.toNat : ℤ) ≥ 5) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - 2 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.minDegree : ℤ) ≥ -4 := by linarith [hn1]
  have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [hn2]
  have s6 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s4, s5]
  have s7 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s6]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by linarith [s1, s2, s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s8, heq_gallai]

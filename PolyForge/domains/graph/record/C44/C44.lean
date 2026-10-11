import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C44 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 4) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by linarith [hn1]
  have s5 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s3, s4]
  have s6 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s5]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [s1, s6]
  linarith [s7]

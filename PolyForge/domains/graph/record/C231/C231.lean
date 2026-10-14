import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C231 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 1) (hn2 : (G.maxDegree : ℤ) ≤ 6) :
    (G.maxDegree : ℤ) ≥ (G.edgeFinset.card : ℤ) - 3 * (G.indepNum : ℤ) + 3 := by
  have s1 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [hn1]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s8 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [hn2]
  have s9 : 6 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (G.maxDegree : ℤ)) :=
      mul_nonneg (by linarith [s7]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s10 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4, s6, s9]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]

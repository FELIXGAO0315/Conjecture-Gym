import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C277 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 4) (hn2 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    2 * (G.maxDegree : ℤ) ≥ (Fintype.card V : ℤ) - 4 * (G.indepNum : ℤ) + 4 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [hn1]
  have s5 : (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (4 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : 2 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s2, s5, s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

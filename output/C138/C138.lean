import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C138 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 1) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 0 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [hn1]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : -2 * (Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [s1, s2, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]

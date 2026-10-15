import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C282 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.indepNum : ℤ) ≤ 4) :
    (G.cliqueNum : ℤ) ≥ (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn2]
  have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
    have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [s1, s2, s3, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

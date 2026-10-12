import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C77 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ (G.chromaticNumber.toNat : ℤ)) (hn2 : (Fintype.card V : ℤ) ≥ 4) :
    (G.cliqueNum : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 12 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s5 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s10 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s10]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : (G.indepNum : ℤ) ≥ 2 := by linarith [s6, s7, s9, s11]
      have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s6, s7, s8, s13]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

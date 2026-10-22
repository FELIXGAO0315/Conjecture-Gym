import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C293 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≥ 2) (hn2 : (Fintype.card V : ℤ) ≥ 6) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 10 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 2 := by linarith [hn1]
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn2]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.indepNum : ℤ) ≥ 2 := by linarith [hn1]
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s9]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by linarith [s6, s7, s8, s11]
      linarith [s12]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

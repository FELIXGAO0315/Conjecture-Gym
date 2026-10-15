import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C316 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) (hn2 : (G.indepNum : ℤ) ≥ 2 * (G.cliqueNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≥ -(G.indepNum : ℤ) + 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s5 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s9 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : -2 * (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
      have s11 : (G.indepNum : ℤ) ≥ 2 := by linarith [s9, s10]
      have s12 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s6, s7, s12]
      have s14 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s13; omega
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

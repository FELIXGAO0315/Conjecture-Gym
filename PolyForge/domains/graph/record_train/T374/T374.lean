import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T374 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≥ (G.minDegree : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 9 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*omega <= 2
      have s6 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s10 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : -(G.indepNum : ℤ) ≥ -1 := by linarith [s9, s10]
      have s12 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s12, s13, s9]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
          mul_nonneg (by linarith [s11]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by linarith [s6, s7, s8, s11, s15]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

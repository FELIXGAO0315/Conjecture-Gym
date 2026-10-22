import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T375 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 8 := by
  have s1 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 8 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*omega <= 2
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.cliqueNum : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s10 : (G.maxDegree : ℤ) ≥ 1 := by linarith [s7, s8, s9]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : -(G.indepNum : ℤ) ≥ -1 := by linarith [s9, s12]
      have s14 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s14, s7, s9]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
          mul_nonneg (by linarith [s13]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 8 := by linarith [s6, s10, s11, s12, s13, s16]
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

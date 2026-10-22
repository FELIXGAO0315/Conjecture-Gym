import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T328 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) (hn2 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - 2 := by
  have s1 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s7 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 2 := by linarith [s2, s3, s4, s5, s6, s7, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s17 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : -4 * (G.minDegree : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s10, s11, s12, s13, s14, s17]
      have s19 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 2 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

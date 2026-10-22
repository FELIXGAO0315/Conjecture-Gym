import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T327 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) (hn2 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 1 := by
  have s1 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -2 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by linarith [s8, s9, s10, s11, s12, s14, s15]
      have s17 : -(G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 0 := by have hr := s16; omega
      have s18 : -4 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 3 := by linarith [s8, s9, s10, s11, s12, s15, s17]
      have s19 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

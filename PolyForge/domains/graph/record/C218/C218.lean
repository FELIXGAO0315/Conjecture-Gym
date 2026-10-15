import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C218 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 4) (hn2 : (G.maxDegree : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.cliqueNum : ℤ) ≤ -(Fintype.card V : ℤ) + 4 * (G.indepNum : ℤ) - 2 := by
  have s1 : -(G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [hn1]
      have s6 : (G.maxDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [s2, s3, s4, s5, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
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
      have s12 : (G.maxDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : (G.indepNum : ℤ) ≥ 2 := by linarith [s10, s14, s11, s12, s16]
      have s18 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s10, s11, s12, s18]
      have s20 : (G.indepNum : ℤ) ≥ 3 := by have hr := s19; omega
      have s21 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s9, s20, s11, s13, s21, s22]
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

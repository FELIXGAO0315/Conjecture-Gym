import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C8 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    (Fintype.card V : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) + 18 := by
  have s1 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 18 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 4
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 18 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 3
      have s7 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 18 := by
        by_cases hc7 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc7; omega
          have s9 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hcc := hc7; omega
          have s12 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s15 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s9, s10, s11, s13, s14]
          have s16 : (G.indepNum : ℤ) ≥ 2 := by have hr := s15; omega
          have s17 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 18 := by linarith [s8, s16, s9, s14]
          linarith [s17]
        · -- 1*chi <= 2
          have s18 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc7; omega
          have s22 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s24 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 18 := by linarith [s18, s19, s22, s23]
          linarith [s24]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C34 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 3) :
    2 * (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s6 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*chi <= 2
          have s7 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s9]) (by linarith [s12])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s7, s8, s9, s10, s11, s13]
          linarith [s14]
      linarith [s2]
    · -- 1*alpha <= 2
      have s15 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc15 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc15; omega
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s21 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s22 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s21]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s16, s17, s18, s19, s20, s22]
          linarith [s23]
        · -- 1*chi <= 2
          have s24 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s25 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s26 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s27 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc15; omega
          have s29 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s27]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s30 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s32 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s31]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : -2 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s24, s25, s26, s29, s32]
          linarith [s33]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

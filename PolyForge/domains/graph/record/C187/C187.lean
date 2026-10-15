import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C187 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≤ 2) :
    2 * (G.diam : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.diam : ℤ) ≥ -2 := by linarith [hn1]
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 8 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 6 := by
        by_cases hc6 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc6; omega
          have s8 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.diam : ℤ) ≥ -2 := by linarith [hn1]
          have s11 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc6; omega
          have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s11]) (by linarith [s12])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : 6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - 4 * (G.diam : ℤ) ≥ 13 := by linarith [s7, s8, s9, s10, s13]
          have s15 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 7 := by have hr := s14; omega
          linarith [s15]
        · -- 1*chi <= 1
          have s16 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s17 : (G.diam : ℤ) ≥ 0 := by positivity
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc6; omega
          have s21 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 6 := by linarith [s16, s17, s18, s21]
          linarith [s22]
      linarith [s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

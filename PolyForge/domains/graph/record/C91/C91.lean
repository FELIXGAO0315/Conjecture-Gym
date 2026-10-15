import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C91 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 5) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 12 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s6 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*chi <= 2
          have s7 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s9 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s12 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s8]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : 9 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.cliqueNum : ℤ) + 9 * (G.indepNum : ℤ) ≥ 37 := by linarith [s7, s8, s9, s10, s12]
          have s14 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by have hr := s13; omega
          linarith [s14]
      linarith [s2]
    · -- 1*alpha <= 2
      have s15 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
        by_cases hc15 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s17 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc15; omega
          have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s21 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s19]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s17, s18, s19, s21]
          have s23 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s22; omega
          have s24 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc15; omega
          have s25 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s16, s23, s24]
          linarith [s25]
        · -- 1*alpha <= 1
          have s26 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s27 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
          have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s30 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc15; omega
          have s32 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s31]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s26, s27, s28, s29, s32]
          linarith [s33]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

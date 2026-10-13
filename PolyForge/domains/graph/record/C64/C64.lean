import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C64 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 4) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 10 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
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
          have s7 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
            by_cases hc7 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc7; omega
              have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s11 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s8, s9, s10]
              linarith [s11]
            · -- 1*chi <= 1
              have s12 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s13 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
              have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc7; omega
              have s16 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
              have s17 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s15])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s12, s13, s14, s15, s17]
              linarith [s18]
          linarith [s7]
      linarith [s2]
    · -- 1*alpha <= 2
      have s19 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by
        by_cases hc19 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s20 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
            by_cases hc20 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s21 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc19; omega
              have s23 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc20; omega
              have s24 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s21, s22, s23]
              linarith [s24]
            · -- 1*alpha <= 1
              have s25 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s26 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
              have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s28 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc20; omega
              have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc19; omega
              have s30 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s28]) (by linarith [s29])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s31 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s25, s26, s27, s28, s30]
              linarith [s31]
          linarith [s20]
        · -- 1*chi <= 2
          have s32 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s33 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
          have s34 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s35 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc19; omega
          have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s37 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s38 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s37]) (by linarith [s36])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s39 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s32, s33, s34, s35, s38]
          linarith [s39]
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C175 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - 4 := by
  have s1 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by
        by_cases hc7 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc7; omega
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s12 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s9, s10, s11, s13]
          have s15 : (G.indepNum : ℤ) ≥ 3 := by have hr := s14; omega
          have s16 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s17 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s18 : -3 * (G.maxDegree : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s8, s15, s9, s10, s16, s17]
          have s19 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 5 := by have hr := s18; omega
          linarith [s19]
        · -- 1*n <= 4
          have s20 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s21 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s24 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s26 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s24]) (by linarith [s25])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 0 := by
            have hw := alpha_le_card_int G
            try push_cast at hw
            linarith [hw]
          have s29 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc7; omega
          have s30 : -(G.indepNum : ℤ) ≥ -4 := by linarith [s28, s29]
          have s31 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s30]) (by linarith [s27])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -5 * (G.maxDegree : ℤ) + 15 * (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) ≥ 18 := by linarith [s20, s21, s22, s23, s26, s31]
          have s33 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s32; omega
          linarith [s33]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T203 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≥ 3 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -8 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -8 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -6 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s6 : -(G.minDegree : ℤ) ≥ -6 := by linarith [hn1]
              have s7 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -6 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*chi <= 2
              have s8 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.minDegree : ℤ) ≥ -6 := by linarith [hn1]
              have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s13 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s13]) (by linarith [s12])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s15 : -6 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ -11 := by linarith [s8, s9, s10, s11, s12, s14]
              have s16 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -5 := by have hr := s15; omega
              linarith [s16]
          linarith [s3]
        · -- 1*alpha <= 2
          have s17 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s20 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s21 : -(G.minDegree : ℤ) ≥ -6 := by linarith [hn1]
          have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s23 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s24 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s23]) (by linarith [s22])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : -6 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ -17 := by linarith [s17, s18, s19, s20, s21, s24]
          have s26 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -8 := by have hr := s25; omega
          linarith [s26]
      linarith [s2]
    · -- 1*alpha <= 1
      have s27 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s28 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s29 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s30 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s31 : -(G.minDegree : ℤ) ≥ -6 := by linarith [hn1]
      have s32 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s33 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s34 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s33]) (by linarith [s32])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s35 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -8 := by linarith [s27, s28, s29, s30, s31, s34]
      linarith [s35]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

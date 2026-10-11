import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C67 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 8 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by
        by_cases hc7 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc7; omega
          have s11 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s8, s9, s10]
          linarith [s11]
        · -- 1*alpha <= 2
          have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc7; omega
          have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s16 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s14]) (by linarith [s15])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s17 : (G.maxDegree : ℤ) = 2 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s18 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s12, s13, s14, s16, s17]
          have s19 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s18; omega
          have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s21 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s21]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s12, s13, s20, s22, s17]
          have s24 : (G.indepNum : ℤ) ≥ 2 := by have hr := s23; omega
          have s25 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s25, s20]
          have s27 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s19, s24, s26]
          linarith [s27]
      linarith [s7]
  linarith [s1]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C36 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.indepNum : ℤ) ≤ 5) :
    (G.maxDegree : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 14 := by
  have s1 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s4 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s5 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s6 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*alpha <= 1
          have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s11 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s9]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s13 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s7, s8, s9, s11, s12]
          linarith [s13]
      linarith [s2]
    · -- 1*chi <= 2
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s16, s15]
      have s18 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s17])
        try push_cast at hw
        linarith [hw]
      have s19 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s21 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s19, s20]
      have s22 : -(G.indepNum : ℤ) ≥ -5 := by linarith [hn1]
      have s23 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s24 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s23]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s25 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s14, s22, s15, s24]
      have s26 : 14 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 40 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (10 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s21]) (by linarith [s25])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s27 : (G.indepNum : ℤ) ≥ 2 := by linarith [s19, s14, s15, s24, s20]
      have s28 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s27]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s29 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s30 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s14, s15, s18, s26, s28, s29]
      have s31 : (G.indepNum : ℤ) ≥ 3 := by have hr := s30; omega
      have s32 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s18, s26, s29]
      have s33 : 15 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 50 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (10 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s32]) (by linarith [s25])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s34 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s31]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s35 : 27 * (G.maxDegree : ℤ) + 54 * (G.chromaticNumber.toNat : ℤ) + 81 * (G.indepNum : ℤ) ≥ 424 := by linarith [s31, s14, s18, s33, s34, s20, s29]
      have s36 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by have hr := s35; omega
      linarith [s36]
  linarith [s1]

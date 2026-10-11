import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C89 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 11 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s3 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s6 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*alpha <= 1
          have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s8 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc2; omega
          have s12 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s11]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s7, s8, s9, s12, s13]
          linarith [s14]
      linarith [s2]
    · -- 1*omega <= 2
      have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
        by_cases hc15 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s16 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s20 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc15; omega
          have s21 : 3 * (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s20]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s22 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s23 : 10 * (G.chromaticNumber.toNat : ℤ) + 15 * (G.indepNum : ℤ) ≥ 58 := by linarith [s16, s17, s18, s21, s22]
          have s24 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by have hr := s23; omega
          linarith [s24]
        · -- 1*alpha <= 2
          have s25 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s27 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s26])
            try push_cast at hw
            linarith [hw]
          have s28 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s29 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc15; omega
          have s30 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s31 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s30]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s25, s28, s29, s31]
          have s33 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s34 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s35 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s33, s34]
          have s36 : 14 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 40 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (10 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s35]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s37 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s38 : (Fintype.card V : ℤ) ≥ 5 := by linarith [s27, s36, s37]
          have s39 : 15 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 50 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (10 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s38]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s40 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s41 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s29]) (by linarith [s40])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s42 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s33, s25, s29, s41, s34]
          have s43 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
              mul_nonneg (by linarith [s29]) (by linarith [s42])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s44 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s25, s29, s27, s36, s43, s37]
          have s45 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s44; omega
          have s46 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s29]) (by linarith [s45])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s47 : 18 * (G.chromaticNumber.toNat : ℤ) + 27 * (G.indepNum : ℤ) ≥ 104 := by linarith [s25, s27, s39, s46, s37]
          have s48 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by have hr := s47; omega
          linarith [s48]
      linarith [s15]
  linarith [s1]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C174 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 4) :
    2 * (G.minDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 4 := by
  have s1 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
    by_cases hc1 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 7
      have s2 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s6 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s7 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
              have s8 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s4, s5, s6, s7]
              linarith [s8]
            · -- 1*chi <= 2
              have s9 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s12 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s12]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s14 : 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s9, s10, s11, s13]
              have s15 : (G.indepNum : ℤ) ≥ 4 := by have hr := s14; omega
              have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s17 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
              have s18 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s16, s17]
              have s19 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s15]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s20 : -4 * (G.minDegree : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 15 := by linarith [s15, s9, s10, s18, s19]
              have s21 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by have hr := s20; omega
              linarith [s21]
          linarith [s3]
        · -- 1*alpha <= 2
          have s22 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
          have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s24 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s25 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s26 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s24]) (by linarith [s25])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 7 := by linarith [s22, s23, s24, s26]
          have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hr := s27; omega
          have s29 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
          have s31 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s29, s30]
          have s32 : 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 4) :=
              mul_nonneg (by linarith [s24]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : -8 * (G.minDegree : ℤ) + 8 * (G.chromaticNumber.toNat : ℤ) + 12 * (G.indepNum : ℤ) ≥ 21 := by linarith [s28, s22, s23, s31, s32]
          have s34 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by have hr := s33; omega
          linarith [s34]
      linarith [s2]
    · -- 1*n <= 6
      have s35 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
        by_cases hc35 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s36 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by
            by_cases hc36 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s37 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s38 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc35; omega
              have s39 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc36; omega
              have s40 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
              have s41 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s37, s38, s39, s40]
              linarith [s41]
            · -- 1*alpha <= 1
              have s42 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s43 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s44 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s45 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc36; omega
              have s46 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc35; omega
              have s47 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s45]) (by linarith [s46])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s48 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by linarith [s42, s43, s44, s45, s47]
              linarith [s48]
          linarith [s36]
        · -- 1*chi <= 2
          have s49 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
            by_cases hc49 : (3 : ℤ) ≤ (G.edgeFinset.card : ℤ)
            · -- 1*m >= 3
              have s50 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s51 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s52 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s53 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc35; omega
              have s54 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s52]) (by linarith [s53])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s55 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s56 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s55, s53]
              have s57 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s56])
                try push_cast at hw
                linarith [hw]
              have s58 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s59 : (G.edgeFinset.card : ℤ) ≥ 3 := by have hcc := hc49; omega
              have s60 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s61 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s62 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [hn1]
              have s63 : 4 * (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s61]) (by linarith [s62])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s64 : 10 * (G.indepNum : ℤ) ≥ 11 := by linarith [s58, s59, s60, s51, s53, s54, s63]
              have s65 : (G.indepNum : ℤ) ≥ 2 := by have hr := s64; omega
              have s66 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s65]) (by linarith [s53])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s67 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc1; omega
              have s68 : 5 * (Fintype.card V : ℤ) ≥ 11 := by linarith [s58, s59, s60, s63]
              have s69 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s68; omega
              have s70 : 9 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 18 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s69]) (by linarith [s67])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s71 : 3 * (Fintype.card V : ℤ) ≥ 10 := by linarith [s59, s57, s70]
              have s72 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s71; omega
              have s73 : 10 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 24 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (6 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s72]) (by linarith [s67])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s74 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s75 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s72]) (by linarith [s74])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s76 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s61]) (by linarith [s67])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s77 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s78 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s77, s62]
              have s79 : -4 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -24 := by
                have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s67]) (by linarith [s78])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s80 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s50, s76, s57, s70, s79]
              have s81 : -3 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -18 := by
                have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s67]) (by linarith [s80])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s82 : -22 * (G.minDegree : ℤ) + 22 * (G.chromaticNumber.toNat : ℤ) + 33 * (G.indepNum : ℤ) ≥ 62 := by linarith [s50, s51, s54, s57, s66, s73, s75, s81]
              have s83 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by have hr := s82; omega
              linarith [s83]
            · -- 1*m <= 2
              have s84 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s85 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s86 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s87 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s88 : -(G.edgeFinset.card : ℤ) ≥ -2 := by have hcc := hc49; omega
              have s89 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s90 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc35; omega
              have s91 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s89]) (by linarith [s90])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s92 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s93 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 0 := by
                have hw := alpha_le_card_int G
                try push_cast at hw
                linarith [hw]
              have s94 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc1; omega
              have s95 : -(G.indepNum : ℤ) ≥ -6 := by linarith [s93, s94]
              have s96 : 6 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ (6 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s95]) (by linarith [s92])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s97 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
                have hw := max_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s98 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s84, s97, s88]
              have s99 : -2 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (2 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s94]) (by linarith [s98])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s100 : -88 * (G.minDegree : ℤ) + 88 * (G.chromaticNumber.toNat : ℤ) + 132 * (G.indepNum : ℤ) ≥ 185 := by linarith [s84, s85, s86, s87, s88, s91, s96, s99]
              have s101 : -2 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s100; omega
              linarith [s101]
          linarith [s49]
      linarith [s35]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C66 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    2 * (G.maxDegree : ℤ) ≥ 3 * (G.minDegree : ℤ) + 2 * (G.cliqueNum : ℤ) - 11 := by
  have s1 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -11 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -11 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -11 := by
            by_cases hc3 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 4
              have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s6 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s7 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s8 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc3; omega
              have s9 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s8]) (by linarith [s7])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s10 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -11 := by linarith [s4, s5, s6, s9]
              linarith [s10]
            · -- 1*n <= 3
              have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_card_int G
                try push_cast at hw
                linarith [hw]
              have s14 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc3; omega
              have s15 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -8 := by linarith [s11, s12, s13, s14]
              linarith [s15]
          linarith [s3]
        · -- 1*omega <= 2
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
          have s19 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s20 : (G.minDegree : ℤ) ≥ 0 := by positivity
          have s21 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s23 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s21, s22]
          have s24 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s23]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s25 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -8 := by linarith [s16, s17, s18, s19, s24]
          linarith [s25]
      linarith [s2]
    · -- 1*chi <= 2
      have s26 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -7 := by
        by_cases hc26 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s27 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -7 := by
            by_cases hc27 : (4 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 4
              have s28 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s29 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s30 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s31 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s32 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s33 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s31, s32]
              have s34 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s35 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc27; omega
              have s36 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s38 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s35, s36, s37]
              have s39 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s38]) (by linarith [s34])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s40 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -7 := by linarith [s28, s29, s30, s33, s39]
              linarith [s40]
            · -- 1*alpha <= 3
              have s41 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s42 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s43 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
              have s44 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s45 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s46 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s44, s45]
              have s47 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s46])
                try push_cast at hw
                linarith [hw]
              have s48 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc26; omega
              have s49 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s50 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc27; omega
              have s51 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s52 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s50]) (by linarith [s51])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s53 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s49, s45, s50, s52]
              have s54 : 9 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 18 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s48]) (by linarith [s53])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s55 : (G.minDegree : ℤ) ≥ 0 := by positivity
              have s56 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s48]) (by linarith [s55])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s57 : -(G.minDegree : ℤ) ≥ -4 := by linarith [s42, s43, s56]
              have s58 : -4 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -24 := by
                have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * (4 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s53]) (by linarith [s57])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s59 : 18 * (G.maxDegree : ℤ) - 27 * (G.minDegree : ℤ) - 18 * (G.cliqueNum : ℤ) ≥ -62 := by linarith [s41, s42, s43, s46, s47, s54, s58]
              have s60 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -6 := by have hr := s59; omega
              linarith [s60]
          linarith [s27]
        · -- 1*n <= 2
          have s61 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s62 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s63 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s64 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc26; omega
          have s65 : 2 * (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -5 := by linarith [s61, s62, s63, s64]
          linarith [s65]
      linarith [s26]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

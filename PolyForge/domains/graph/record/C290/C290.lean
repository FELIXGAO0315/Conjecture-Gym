import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C290 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.cliqueNum : ℤ) ≥ -3 * (Fintype.card V : ℤ) - 3 * (G.maxDegree : ℤ) + 21 := by
  have s1 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 21 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 23 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 23 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
            · -- 1*omega >= 3
              have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
              have s6 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s7 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 30 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*omega <= 2
              have s8 : (G.cliqueNum : ℤ) ≥ 1 := by
                have hw := omega_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s9 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
              have s10 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s13 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s14 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s12, s13]
              have s15 : 2 * (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * (2 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s14])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s16 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 23 := by linarith [s8, s9, s10, s11, s15]
              linarith [s16]
          linarith [s3]
        · -- 1*chi <= 2
          have s17 : (G.cliqueNum : ℤ) ≥ 1 := by
            have hw := omega_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
          have s19 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s20 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s21 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s24 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s21, s22, s23]
          have s25 : 2 * (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 12 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s18]) (by linarith [s24])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s26 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 23 := by linarith [s17, s18, s19, s20, s25]
          linarith [s26]
      linarith [s2]
    · -- 1*n <= 5
      have s27 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 21 := by
        by_cases hc27 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s28 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 21 := by
            by_cases hc28 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
            · -- 1*omega >= 3
              have s29 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc28; omega
              have s30 : (Fintype.card V : ℤ) ≥ 3 := by
                have hw := three_le_card_of_cycle_int G hp1
                try push_cast at hw
                linarith [hw]
              have s31 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
                have hw := omega_le_maxdeg_add_one_int G
                try push_cast at hw
                linarith [hw]
              have s32 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 21 := by linarith [s29, s30, s31]
              linarith [s32]
            · -- 1*omega <= 2
              have s33 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s34 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s35 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s36 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s37 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
              have s38 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s37]) (by linarith [s36])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s39 : 5 * (G.cliqueNum : ℤ) ≥ 6 := by linarith [s33, s34, s35, s38]
              have s40 : (G.cliqueNum : ℤ) ≥ 2 := by have hr := s39; omega
              have s41 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc28; omega
              have s42 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s41])
                try push_cast at hw
                linarith [hw]
              have s43 : (Fintype.card V : ℤ) ≥ 3 := by
                have hw := three_le_card_of_cycle_int G hp1
                try push_cast at hw
                linarith [hw]
              have s44 : 8 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 15 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s43]) (by linarith [s37])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s45 : 8 * (Fintype.card V : ℤ) ≥ 27 := by linarith [s33, s42, s44]
              have s46 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s45; omega
              have s47 : 5 * (G.maxDegree : ℤ) ≥ 6 := by linarith [s33, s34, s38]
              have s48 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s47; omega
              have s49 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 22 := by linarith [s40, s46, s48]
              linarith [s49]
          linarith [s28]
        · -- 1*chi <= 2
          have s50 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s51 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s52 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s53 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s54 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
          have s55 : 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (5 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s54]) (by linarith [s53])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s56 : 5 * (G.cliqueNum : ℤ) ≥ 6 := by linarith [s50, s51, s52, s55]
          have s57 : (G.cliqueNum : ℤ) ≥ 2 := by have hr := s56; omega
          have s58 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s59 : 8 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 15 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (5 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s58]) (by linarith [s54])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s60 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s61 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc27; omega
          have s62 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s60, s61]
          have s63 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s62])
            try push_cast at hw
            linarith [hw]
          have s64 : 8 * (Fintype.card V : ℤ) ≥ 27 := by linarith [s50, s59, s63]
          have s65 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s64; omega
          have s66 : 5 * (G.maxDegree : ℤ) ≥ 6 := by linarith [s50, s51, s55]
          have s67 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s66; omega
          have s68 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 22 := by linarith [s57, s65, s67]
          linarith [s68]
      linarith [s27]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

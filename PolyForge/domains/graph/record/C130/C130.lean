import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C130 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (G.cliqueNum : ℤ) ≥ -3 * (Fintype.card V : ℤ) - 3 * (G.maxDegree : ℤ) + 18 := by
  have s1 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 18 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 18 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s6 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 18 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*omega <= 2
          have s7 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 19 := by
            by_cases hc7 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 5
              have s8 : (G.cliqueNum : ℤ) ≥ 1 := by
                have hw := omega_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s9 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc7; omega
              have s10 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s13 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s14 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [s12, s13]
              have s15 : 4 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (4 - (G.maxDegree : ℤ)) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s14])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s16 : 15 * (Fintype.card V : ℤ) + 15 * (G.maxDegree : ℤ) + 5 * (G.cliqueNum : ℤ) ≥ 98 := by linarith [s8, s9, s10, s11, s15]
              have s17 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 20 := by have hr := s16; omega
              linarith [s17]
            · -- 1*n <= 4
              have s18 : (G.edgeFinset.card : ℤ) ≥ 3 := by
                have hw := three_le_edges_int G hp1
                try push_cast at hw
                linarith [hw]
              have s19 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s20 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s19])
                try push_cast at hw
                linarith [hw]
              have s21 : (Fintype.card V : ℤ) ≥ 3 := by
                have hw := three_le_card_of_cycle_int G hp1
                try push_cast at hw
                linarith [hw]
              have s22 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc7; omega
              have s23 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s21]) (by linarith [s22])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s24 : 7 * (Fintype.card V : ℤ) ≥ 24 := by linarith [s18, s20, s23]
              have s25 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s24; omega
              have s26 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s27 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s28 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s22]) (by linarith [s27])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s29 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s18, s26, s28]
              have s30 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s29; omega
              have s31 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s32 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 19 := by linarith [s25, s30, s31]
              linarith [s32]
          linarith [s7]
      linarith [s2]
    · -- 1*chi <= 2
      have s33 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 19 := by
        by_cases hc33 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s34 : (G.cliqueNum : ℤ) ≥ 1 := by
            have hw := omega_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s35 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc33; omega
          have s36 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s37 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s38 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s39 : -(G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s40 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s41 : -(G.maxDegree : ℤ) ≥ -4 := by linarith [s38, s39, s40]
          have s42 : 4 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 20 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (4 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s35]) (by linarith [s41])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s43 : 15 * (Fintype.card V : ℤ) + 15 * (G.maxDegree : ℤ) + 5 * (G.cliqueNum : ℤ) ≥ 98 := by linarith [s34, s35, s36, s37, s42]
          have s44 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 20 := by have hr := s43; omega
          linarith [s44]
        · -- 1*n <= 4
          have s45 : (G.cliqueNum : ℤ) ≥ 1 := by
            have hw := omega_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s46 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s47 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s48 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc33; omega
          have s49 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s47]) (by linarith [s48])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s50 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s51 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s52 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s50, s51]
          have s53 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s52])
            try push_cast at hw
            linarith [hw]
          have s54 : 7 * (Fintype.card V : ℤ) ≥ 24 := by linarith [s46, s49, s53]
          have s55 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s54; omega
          have s56 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s57 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s58 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s48]) (by linarith [s57])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s59 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s46, s56, s58]
          have s60 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s59; omega
          have s61 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 19 := by linarith [s45, s55, s60]
          linarith [s61]
      linarith [s33]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

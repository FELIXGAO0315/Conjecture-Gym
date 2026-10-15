import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C267 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (Fintype.card V : ℤ) ≥ -3 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 15 := by
  have s1 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s5 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s6 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s7 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*omega <= 2
          have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s9 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s12 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s13 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s14 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s12, s13]
          have s15 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s11]) (by linarith [s14])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by linarith [s8, s9, s10, s15]
          linarith [s16]
      linarith [s2]
    · -- 1*chi <= 2
      have s17 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by
        by_cases hc17 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 5
          have s18 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc17; omega
          have s20 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s21 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s24 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s18, s22, s23]
          have s25 : 2 * (Fintype.card V : ℤ) + 5 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 10 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * (2 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s24])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s26 : 10 * (Fintype.card V : ℤ) + 15 * (G.maxDegree : ℤ) + 5 * (G.chromaticNumber.toNat : ℤ) ≥ 74 := by linarith [s18, s19, s20, s21, s22, s25]
          have s27 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 15 := by have hr := s26; omega
          linarith [s27]
        · -- 1*n <= 4
          have s28 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s29 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s30 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s32 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s33 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc17; omega
          have s34 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
              mul_nonneg (by linarith [s33]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s35 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s28, s29, s30, s31, s34]
          have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s35; omega
          have s37 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s38 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s37]) (by linarith [s33])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s39 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s40 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s28, s39]
          have s41 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s40])
            try push_cast at hw
            linarith [hw]
          have s42 : 7 * (Fintype.card V : ℤ) ≥ 24 := by linarith [s29, s38, s41]
          have s43 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s42; omega
          have s44 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s29, s30, s34]
          have s45 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s44; omega
          have s46 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 16 := by linarith [s36, s43, s45]
          linarith [s46]
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

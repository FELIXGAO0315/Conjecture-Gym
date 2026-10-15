import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C153 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 4) :
    (G.girth : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 8 := by
    by_cases hc1 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 7
      have s2 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 10 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
          have s5 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [hn1]
          have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 11 := by linarith [s3, s4, s5, s6, s7]
          linarith [s8]
        · -- 1*chi <= 2
          have s9 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s12 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s9, s10, s11, s13]
          have s15 : (G.indepNum : ℤ) ≥ 4 := by have hr := s14; omega
          have s16 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s17 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s18 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 10 := by linarith [s15, s16, s10, s11, s17]
          linarith [s18]
      linarith [s2]
    · -- 1*n <= 6
      have s19 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 8 := by
        by_cases hc19 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s20 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.vertexCoverNum.toNat : ℤ) ≥ -4 := by linarith [hn1]
          have s23 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s25 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc1; omega
          have s26 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [s24, s25]
          have s27 : (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s23]) (by linarith [s26])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc19; omega
          have s29 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s30 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.indepNum : ℤ) ≥ -6 := by linarith [s29, s25, s30]
          have s32 : 6 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 18 := by
            have hmul : (0 : ℤ) ≤ (6 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s31]) (by linarith [s28])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : 42 * (G.chromaticNumber.toNat : ℤ) + 42 * (G.indepNum : ℤ) - 14 * (G.girth : ℤ) ≥ 117 := by linarith [s20, s21, s22, s27, s32, s30]
          have s34 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 9 := by have hr := s33; omega
          linarith [s34]
        · -- 1*chi <= 2
          have s35 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s36 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s38 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s39 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc1; omega
          have s40 : 9 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 18 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s38]) (by linarith [s39])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s41 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s42 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc19; omega
          have s43 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s41, s42]
          have s44 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s43])
            try push_cast at hw
            linarith [hw]
          have s45 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s46 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s45]) (by linarith [s42])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s47 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s38, s37, s42, s46]
          have s48 : (G.indepNum : ℤ) ≥ 2 := by have hr := s47; omega
          have s49 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s48]) (by linarith [s42])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s50 : 9 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) - 3 * (G.girth : ℤ) ≥ 23 := by linarith [s35, s36, s37, s40, s44, s49]
          have s51 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 8 := by have hr := s50; omega
          linarith [s51]
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

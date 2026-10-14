import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C175 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.girth : ℤ) ≥ 5) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 12 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4]
          linarith [s5]
        · -- 1*chi <= 2
          have s6 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s7 : (G.girth : ℤ) ≥ 5 := by linarith [hn1]
          have s8 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s11 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s6]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : 6 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 37 := by linarith [s6, s7, s8, s9, s11]
          have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by have hr := s12; omega
          linarith [s13]
      linarith [s2]
    · -- 1*alpha <= 2
      have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
        by_cases hc14 : (4 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 4
          have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
            by_cases hc15 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s16 : (G.girth : ℤ) ≥ 5 := by linarith [hn1]
              have s17 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
                have hw := girth_le_card_int G hp1
                try push_cast at hw
                linarith [hw]
              have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s19 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc15; omega
              have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s21 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s20])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s22 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s16, s17, s18, s19, s21]
              have s23 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s22; omega
              have s24 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc15; omega
              have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s23, s24]
              linarith [s25]
            · -- 1*alpha <= 1
              have s26 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s27 : (G.girth : ℤ) ≥ 5 := by linarith [hn1]
              have s28 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
                have hw := girth_le_card_int G hp1
                try push_cast at hw
                linarith [hw]
              have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s30 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s31 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc15; omega
              have s32 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s31]) (by linarith [s30])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s33 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s26, s27, s28, s29, s32]
              linarith [s33]
          linarith [s15]
        · -- 1*m <= 3
          have s34 : (G.girth : ℤ) ≥ 5 := by linarith [hn1]
          have s35 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s36 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s37 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s38 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s39 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s37]) (by linarith [s38])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s40 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s34, s35, s36, s37, s39]
          have s41 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s40; omega
          have s42 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s43 : -(G.edgeFinset.card : ℤ) ≥ -3 := by have hcc := hc14; omega
          have s44 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s45 : (G.indepNum : ℤ) ≥ 2 := by linarith [s34, s42, s35, s43, s44]
          have s46 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s41, s45]
          linarith [s46]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

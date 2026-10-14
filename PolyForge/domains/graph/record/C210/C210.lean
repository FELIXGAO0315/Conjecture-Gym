import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C210 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ 3) :
    2 * (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s5 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s6 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*chi <= 2
          have s7 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s10 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s11 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s10]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : (G.indepNum : ℤ) ≥ 3 := by linarith [s7, s8, s9, s11]
          have s13 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
          have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s15 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s12, s7, s8, s13, s14]
          linarith [s15]
      linarith [s2]
    · -- 1*n <= 5
      have s16 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc16 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s17 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by
            by_cases hc17 : (3 : ℤ) ≤ (G.vertexCoverNum.toNat : ℤ)
            · -- 1*tau >= 3
              have s18 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hcc := hc17; omega
              have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s20 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc16; omega
              have s22 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
              have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s24 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s18, s22, s23]
              have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s24]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s26 : -4 * (G.maxDegree : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 15 := by linarith [s18, s19, s20, s25, s23]
              have s27 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by have hr := s26; omega
              linarith [s27]
            · -- 1*tau <= 2
              have s28 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s29 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s30 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc16; omega
              have s31 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hcc := hc17; omega
              have s32 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s33 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by linarith [s28, s29, s30, s31, s32]
              linarith [s33]
          linarith [s17]
        · -- 1*chi <= 2
          have s34 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
            by_cases hc34 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s35 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc34; omega
              have s37 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s38 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s39 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s40 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc34; omega
              have s41 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s39]) (by linarith [s40])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s42 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s35, s36, s37, s38, s41]
              linarith [s42]
            · -- 1*chi <= 1
              have s43 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s44 : (Fintype.card V : ℤ) ≥ 1 := by
                have hw := card_ge_one_int (V := V)
                try push_cast at hw
                linarith [hw]
              have s45 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s46 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s47 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc34; omega
              have s48 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s46]) (by linarith [s47])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s49 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s43, s44, s45, s48]
              linarith [s49]
          linarith [s34]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

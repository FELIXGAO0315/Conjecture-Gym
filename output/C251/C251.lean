import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C251 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 5) (hn2 : (G.maxDegree : ℤ) ≥ (G.chromaticNumber.toNat : ℤ)) :
    (G.maxDegree : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 17 := by
  have s1 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 2
      have s2 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by
        by_cases hc2 : (4 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 4
          have s3 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 19 := by
            by_cases hc3 : (5 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 5
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.indepNum : ℤ) ≥ 5 := by have hcc := hc3; omega
              have s6 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s7 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 19 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*alpha <= 4
              have s8 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
              have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s10 : -(G.indepNum : ℤ) ≥ -4 := by have hcc := hc3; omega
              have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s12 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s10]) (by linarith [s11])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s13 : 4 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s8, s9, s10, s12]
              have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s13; omega
              have s15 : (G.indepNum : ℤ) ≥ 4 := by have hcc := hc3; omega
              have s16 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s17 : 4 * (G.maxDegree : ℤ) ≥ 5 := by linarith [s8, s9, s16, s10, s12]
              have s18 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s17; omega
              have s19 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 20 := by linarith [s14, s15, s18]
              linarith [s19]
          linarith [s3]
        · -- 1*alpha <= 3
          have s20 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by
            by_cases hc20 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc20; omega
              have s22 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
              have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s24 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s25 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s26 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by
                have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s25]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s27 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by linarith [s21, s22, s23, s24, s26]
              linarith [s27]
            · -- 1*chi <= 2
              have s28 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
              have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s30 : -(G.indepNum : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s31 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s32 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
                have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s30]) (by linarith [s31])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s33 : 3 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s28, s29, s30, s32]
              have s34 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s33; omega
              have s35 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc20; omega
              have s36 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s37 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s36]) (by linarith [s35])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s38 : 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s28, s29, s35, s37]
              have s39 : (G.indepNum : ℤ) ≥ 3 := by have hr := s38; omega
              have s40 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
              have s41 : 3 * (G.maxDegree : ℤ) ≥ 5 := by linarith [s28, s29, s40, s30, s32]
              have s42 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s41; omega
              have s43 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 17 := by linarith [s34, s39, s42]
              linarith [s43]
          linarith [s20]
      linarith [s2]
    · -- 1*m <= 1
      have s44 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
      have s45 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s46 : (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s47 : (G.maxDegree : ℤ) ≥ 1 := by linarith [s45, s46]
      have s48 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s49 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s50 : -(G.edgeFinset.card : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s51 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by linarith [s49, s46, s50]
      have s52 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s53 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s54 : (G.indepNum : ℤ) ≥ 4 := by linarith [s44, s52, s50, s53]
      have s55 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s54]) (by linarith [s51])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s56 : (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 19 := by linarith [s44, s47, s48, s51, s55]
      linarith [s56]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

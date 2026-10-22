import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T147 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 3) :
    (G.chromaticNumber.toNat : ℤ) ≥ 3 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 0 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s3 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s6 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s7 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s4, s5, s6]
              linarith [s7]
            · -- 1*chi <= 2
              have s8 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s10]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s15 : -9 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 4 := by linarith [s8, s9, s10, s11, s12, s14]
              have s16 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by have hr := s15; omega
              linarith [s16]
          linarith [s3]
        · -- 1*alpha <= 2
          have s17 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 0 := by
            by_cases hc17 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc17; omega
              have s19 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
              have s20 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s21 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 0 := by linarith [s18, s19, s20]
              linarith [s21]
            · -- 1*chi <= 2
              have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
                have hw := min_le_max_int G
                try push_cast at hw
                linarith [hw]
              have s23 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s24 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
              have s25 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
                have hw := handshake_min_int G
                try push_cast at hw
                linarith [hw]
              have s26 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s27 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc17; omega
              have s28 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s24]) (by linarith [s27])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s29 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                try push_cast at hw
                linarith [hw]
              have s30 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s29, s27]
              have s31 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
                have hw := turan_r2_int G (by linarith [s30])
                try push_cast at hw
                linarith [hw]
              have s32 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
              have s33 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s34 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s24, s32, s33]
              have s35 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s37 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s35]) (by linarith [s36])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s38 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s26, s35, s27, s37]
              have s39 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 8 := by
                have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (4 - (Fintype.card V : ℤ)) :=
                  mul_nonneg (by linarith [s34]) (by linarith [s38])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s40 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
              have s41 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
                have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
                  mul_nonneg (by linarith [s38]) (by linarith [s40])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s42 : -6 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 3 := by linarith [s22, s23, s24, s25, s26, s28, s31, s39, s41]
              have s43 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by have hr := s42; omega
              linarith [s43]
          linarith [s17]
      linarith [s2]
    · -- 1*alpha <= 1
      have s44 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s45 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s46 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s47 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s48 : -(G.minDegree : ℤ) ≥ -3 := by linarith [hn1]
      have s49 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s50 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s51 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s50]) (by linarith [s49])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s52 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s44, s45, s46, s47, s48, s51]
      linarith [s52]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

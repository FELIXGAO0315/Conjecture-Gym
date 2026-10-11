import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C5 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 11 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
        by_cases hc2 : (4 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 4
          have s3 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
            by_cases hc3 : (3 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 3
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s5 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc3; omega
              have s6 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s4, s5]
              linarith [s6]
            · -- 1*alpha <= 2
              have s7 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
              have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s9 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc3; omega
              have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s11 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s10])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s12 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s7, s8, s9, s11]
              have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s9]) (by linarith [s12])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s7, s8, s13]
              linarith [s14]
          linarith [s3]
        · -- 1*m <= 3
          have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
            by_cases hc15 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc15; omega
              have s17 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
              have s18 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
                have hw := tau_le_edges_int G
                try push_cast at hw
                linarith [hw]
              have s19 : -(G.edgeFinset.card : ℤ) ≥ -3 := by have hcc := hc2; omega
              have s20 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s21 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s16, s17, s18, s19, s20]
              linarith [s21]
            · -- 1*chi <= 2
              have s22 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
              have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s24 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc15; omega
              have s25 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s26 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s25]) (by linarith [s24])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s28 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s22, s23, s24, s26, s27]
              linarith [s28]
          linarith [s15]
      linarith [s2]
    · -- 1*n <= 5
      have s29 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
      have s30 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s31 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s32 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s33 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s34 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s32, s33]
      have s35 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s31]) (by linarith [s34])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s36 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s37 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s29, s33, s36]
      have s38 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s39 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s37]) (by linarith [s38])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s40 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s29, s30, s39, s36]
      have s41 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s40; omega
      have s42 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
          mul_nonneg (by linarith [s37]) (by linarith [s41])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s43 : 12 * (G.chromaticNumber.toNat : ℤ) + 18 * (G.indepNum : ℤ) ≥ 61 := by linarith [s29, s30, s35, s42, s36]
      have s44 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by have hr := s43; omega
      linarith [s44]
  linarith [s1]

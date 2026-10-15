import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C231 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 3) :
    2 * (G.diam : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 3 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 3 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.diam : ℤ)
    · -- 1*diam >= 2
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 3 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s5 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [hn1]
          have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s8 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6, s7]
          linarith [s8]
        · -- 1*chi <= 2
          have s9 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [hn1]
          have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s13 : (G.diam : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s14 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s14]) (by linarith [s12])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s9, s13, s10, s12, s15]
          have s17 : (G.indepNum : ℤ) ≥ 2 := by have hr := s16; omega
          have s18 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s17]) (by linarith [s12])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s20 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 3 := by linarith [s9, s10, s11, s18, s19]
          linarith [s20]
      linarith [s2]
    · -- 1*diam <= 1
      have s21 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 5 := by
        by_cases hc21 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc21; omega
          have s23 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : -(G.diam : ℤ) ≥ -1 := by have hcc := hc1; omega
          have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 7 := by linarith [s22, s23, s24]
          linarith [s25]
        · -- 1*chi <= 2
          have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s27 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s29 : -(G.diam : ℤ) ≥ -1 := by have hcc := hc1; omega
          have s30 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc21; omega
          have s32 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s30]) (by linarith [s31])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s33 : 4 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - 4 * (G.diam : ℤ) ≥ 9 := by linarith [s26, s27, s28, s29, s32]
          have s34 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) ≥ 5 := by have hr := s33; omega
          linarith [s34]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

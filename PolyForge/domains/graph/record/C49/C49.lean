import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C49 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.vertexCoverNum.toNat : ℤ) ≥ -(Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 9 := by
  have s1 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by
    by_cases hc1 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 3
      have s2 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s7 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*chi <= 2
          have s8 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
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
          have s14 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s8, s9, s11, s13]
          have s15 : (G.indepNum : ℤ) ≥ 2 := by have hr := s14; omega
          have s16 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s18 : 2 * (Fintype.card V : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 17 := by linarith [s8, s9, s10, s16, s17]
          have s19 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by have hr := s18; omega
          linarith [s19]
      linarith [s2]
    · -- 1*n <= 2
      have s20 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : -(G.indepNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s23 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s20, s21, s22]
      have s24 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s23; omega
      have s25 : 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [s20, s21]
      have s26 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by have hr := s25; omega
      have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s28 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s29 : -3 * (G.indepNum : ℤ) ≥ -4 := by linarith [s21, s28, s22]
      have s30 : -(G.indepNum : ℤ) ≥ -1 := by have hr := s29; omega
      have s31 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s32 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s30]) (by linarith [s31])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s33 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by linarith [s24, s26, s27, s30, s32]
      linarith [s33]
  linarith [s1]

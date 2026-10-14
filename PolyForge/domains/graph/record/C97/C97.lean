import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C97 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 4) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (Fintype.card V : ℤ) + 24 := by
  have s1 : 3 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 24 := by
    by_cases hc1 : (7 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 7
      have s2 : 3 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 27 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (Fintype.card V : ℤ) ≥ 7 := by have hcc := hc1; omega
          have s5 : 3 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 27 := by linarith [s3, s4]
          linarith [s5]
        · -- 1*chi <= 2
          have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
          have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s9 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s9]) (by linarith [s8])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s12 : 3 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 28 := by linarith [s6, s7, s8, s10, s11]
          linarith [s12]
      linarith [s2]
    · -- 1*n <= 6
      have s13 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(Fintype.card V : ℤ) ≥ -6 := by have hcc := hc1; omega
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [s16, s17]
      have s19 : (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s21 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s13, s17, s20]
      have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s23 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s21]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s13, s14, s23, s20]
      have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
          mul_nonneg (by linarith [s21]) (by linarith [s24])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s26 : 12 * (Fintype.card V : ℤ) + 8 * (G.chromaticNumber.toNat : ℤ) ≥ 93 := by linarith [s13, s14, s19, s25, s20]
      have s27 : 3 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 24 := by have hr := s26; omega
      linarith [s27]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

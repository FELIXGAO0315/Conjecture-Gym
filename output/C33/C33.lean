import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C33 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 6) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 14 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s3, s4]
          linarith [s5]
        · -- 1*chi <= 2
          have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s7 : (G.maxDegree : ℤ) ≥ 6 := by linarith [hn1]
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s11 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s10]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s6, s7, s8, s9, s11]
          have s13 : (G.indepNum : ℤ) ≥ 4 := by have hr := s12; omega
          have s14 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s6, s7]
          have s15 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s13]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : 4 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 31 := by linarith [s13, s14, s8, s15]
          have s17 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by have hr := s16; omega
          linarith [s17]
      linarith [s2]
    · -- 1*alpha <= 2
      have s18 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.maxDegree : ℤ) ≥ 6 := by linarith [hn1]
      have s20 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s21 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s23 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s21]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 7 := by linarith [s18, s19, s20, s21, s23]
      have s25 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hr := s24; omega
      have s26 : (Fintype.card V : ℤ) ≥ 7 := by linarith [s18, s19]
      have s27 : 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 4) :=
          mul_nonneg (by linarith [s21]) (by linarith [s25])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s28 : 8 * (G.chromaticNumber.toNat : ℤ) + 12 * (G.indepNum : ℤ) ≥ 53 := by linarith [s25, s26, s20, s27]
      have s29 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by have hr := s28; omega
      linarith [s29]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

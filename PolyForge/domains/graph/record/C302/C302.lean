import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C302 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 3) :
    (G.girth : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
        have hw := girth_le_card_int G hp1
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -3 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 7 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 6 := by
        by_cases hc8 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s9 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s12 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc8; omega
          have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s12]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 6 := by linarith [s9, s10, s13]
          linarith [s14]
        · -- 1*alpha <= 2
          have s15 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s16 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s20 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s18]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc8; omega
          have s23 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s22]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s24 : 9 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - 3 * (G.girth : ℤ) ≥ 16 := by linarith [s15, s16, s17, s20, s23]
          have s25 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.girth : ℤ) ≥ 6 := by have hr := s24; omega
          linarith [s25]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

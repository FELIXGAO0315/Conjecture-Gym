import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C236 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.girth : ℤ) ≤ 5) :
    2 * (G.girth : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 4 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.girth : ℤ) ≥ 4 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.girth : ℤ) ≥ 4 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s5 : -(G.girth : ℤ) ≥ -5 := by linarith [hn1]
          have s6 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.girth : ℤ) ≥ 5 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*chi <= 2
          have s7 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
            have hw := girth_le_card_int G hp1
            try push_cast at hw
            linarith [hw]
          have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s9 : -(G.girth : ℤ) ≥ -5 := by linarith [hn1]
          have s10 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
          have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s12 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s10]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : 6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - 4 * (G.girth : ℤ) ≥ 7 := by linarith [s7, s8, s9, s12]
          have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.girth : ℤ) ≥ 4 := by have hr := s13; omega
          linarith [s14]
      linarith [s2]
    · -- 1*alpha <= 1
      have s15 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
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
      have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s20 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s19]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.girth : ℤ) ≥ 6 := by linarith [s15, s16, s17, s20]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C229 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≤ 5) :
    (G.radius.toNat : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 5 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 8 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G hp1
            try push_cast at hw
            linarith [hw]
          have s6 : -(G.diam : ℤ) ≥ -5 := by linarith [hn1]
          have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 10 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*chi <= 2
          have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s9 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
            have hw := radius_le_diam_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp1
            try push_cast at hw
            linarith [hw]
          have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s12 : -(G.diam : ℤ) ≥ -5 := by linarith [hn1]
          have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s14 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s8]) (by linarith [s13])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 8 := by linarith [s8, s9, s10, s11, s12, s14]
          linarith [s15]
      linarith [s2]
    · -- 1*alpha <= 2
      have s16 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s22 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s21]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s23 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by linarith [s16, s17, s18, s19, s22]
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

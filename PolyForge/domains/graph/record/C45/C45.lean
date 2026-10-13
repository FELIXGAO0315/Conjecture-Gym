import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C45 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 1) :
    (G.diam : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp2
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 13 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 8 := by
        by_cases hc8 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s10 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc8; omega
          have s11 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp2
            try push_cast at hw
            linarith [hw]
          have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s10]) (by linarith [s13])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s15 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 8 := by linarith [s9, s10, s11, s12, s14]
          linarith [s15]
        · -- 1*alpha <= 1
          have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s18 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := connected_min_deg_int G hp2 hp1
            try push_cast at hw
            linarith [hw]
          have s19 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
            have hw := diam_le_card_sub_one_int G hp2
            try push_cast at hw
            linarith [hw]
          have s20 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc8; omega
          have s23 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s22]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s24 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 8 := by linarith [s16, s17, s18, s19, s20, s23]
          linarith [s24]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

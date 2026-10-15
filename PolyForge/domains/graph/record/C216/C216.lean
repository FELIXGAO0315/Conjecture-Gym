import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C216 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 1) :
    2 * (G.radius.toNat : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.diam : ℤ)
    · -- 1*diam >= 1
      have s2 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by
        by_cases hc2 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 3
          have s3 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 8 := by
            by_cases hc3 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc3; omega
              have s5 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s6 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s7 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s8 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
              have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s10 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 8 := by linarith [s4, s5, s6, s7, s8, s9]
              linarith [s10]
            · -- 1*chi <= 1
              have s11 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc2; omega
              have s13 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc3; omega
              have s17 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s15]) (by linarith [s16])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 8 := by linarith [s11, s12, s13, s14, s17]
              linarith [s18]
          linarith [s3]
        · -- 1*n <= 2
          have s19 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by
            by_cases hc19 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s20 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc19; omega
              have s22 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s23 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s24 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
              have s25 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s26 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s20, s21, s22, s23, s24, s25]
              linarith [s26]
            · -- 1*chi <= 1
              have s27 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s28 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s29 : (G.diam : ℤ) ≥ 1 := by have hcc := hc1; omega
              have s30 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s31 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s32 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc19; omega
              have s33 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s31]) (by linarith [s32])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s34 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s27, s28, s29, s30, s33]
              linarith [s34]
          linarith [s19]
      linarith [s2]
    · -- 1*diam <= 0
      have s35 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s36 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s37 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s38 : -(G.diam : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s39 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by linarith [s35, s36, s37, s38]
      linarith [s39]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

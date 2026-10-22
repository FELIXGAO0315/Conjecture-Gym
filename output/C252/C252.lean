import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C252 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.radius.toNat : ℤ) ≤ 3) :
    2 * (G.radius.toNat : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.radius.toNat : ℤ) ≥ -3 := by linarith [hn1]
      have s6 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*omega <= 2
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by
        by_cases hc7 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by
            by_cases hc8 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc8; omega
              have s10 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc7; omega
              have s11 : -(G.radius.toNat : ℤ) ≥ -3 := by linarith [hn1]
              have s12 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 12 := by linarith [s9, s10, s11]
              linarith [s12]
            · -- 1*chi <= 2
              have s13 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc7; omega
              have s14 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s15 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s17 : -(G.radius.toNat : ℤ) ≥ -3 := by linarith [hn1]
              have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc8; omega
              have s19 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s13]) (by linarith [s18])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s20 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s13, s14, s15, s16, s17, s19]
              linarith [s20]
          linarith [s8]
        · -- 1*alpha <= 2
          have s21 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by
            by_cases hc21 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc21; omega
              have s23 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s24 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s25 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s26 : -(G.radius.toNat : ℤ) ≥ -3 := by linarith [hn1]
              have s27 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc7; omega
              have s28 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
                  mul_nonneg (by linarith [s27]) (by linarith [s22])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s29 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 7 := by linarith [s22, s23, s24, s25, s26, s28]
              linarith [s29]
            · -- 1*chi <= 2
              have s30 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
                have hw := radius_le_diam_int G hp1
                try push_cast at hw
                linarith [hw]
              have s31 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
                have hw := diam_le_card_sub_one_int G hp1
                try push_cast at hw
                linarith [hw]
              have s32 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s33 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s34 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc21; omega
              have s35 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s33]) (by linarith [s34])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s36 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s37 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc7; omega
              have s38 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s37]) (by linarith [s36])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s39 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.radius.toNat : ℤ) ≥ 6 := by linarith [s30, s31, s32, s35, s38]
              linarith [s39]
          linarith [s21]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

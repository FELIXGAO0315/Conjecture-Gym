import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C191 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 4) :
    (G.indepNum : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) + 7 := by
  have s1 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
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
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*omega <= 2
      have s7 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
        by_cases hc7 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s8 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by
            by_cases hc8 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc8; omega
              have s10 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 10 := by linarith [s9, s10, s11]
              linarith [s12]
            · -- 1*chi <= 2
              have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc8; omega
              have s14 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s16 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc8; omega
              have s18 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s17])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s20 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by linarith [s13, s14, s15, s18, s19]
              linarith [s20]
          linarith [s8]
        · -- 1*chi <= 1
          have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn1]
          have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s24 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc7; omega
          have s26 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s24]) (by linarith [s25])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s27 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s28 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s21, s22, s23, s26, s27]
          linarith [s28]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

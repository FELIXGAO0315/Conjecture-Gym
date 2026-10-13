import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C92 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 1) :
    2 * (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s2, s3, s4, s5, s6, s7]
      linarith [s8]
    · -- 1*omega <= 2
      have s9 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc9 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
        · -- 1*max_deg >= 1
          have s10 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by
            by_cases hc10 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s11 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := chi_le_n_int G
                try push_cast at hw
                linarith [hw]
              have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc10; omega
              have s14 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s16 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s11, s12, s13, s14, s15]
              linarith [s16]
            · -- 1*chi <= 1
              have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s18 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc9; omega
              have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s20 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc10; omega
              have s22 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s20]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s23 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s17, s18, s19, s22]
              linarith [s23]
          linarith [s10]
        · -- 1*max_deg <= 0
          have s24 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s26 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc9; omega
          have s27 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s24, s25, s26]
          linarith [s27]
      linarith [s9]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

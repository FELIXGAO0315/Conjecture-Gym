import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C63 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 1) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.maxDegree : ℤ) - 3 * (G.indepNum : ℤ) + 5 := by
  have s1 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 1
      have s2 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
          have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s8 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by linarith [s3, s4, s5, s6, s7]
          linarith [s8]
        · -- 1*chi <= 2
          have s9 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by
            by_cases hc9 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
            · -- 1*n >= 3
              have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s12 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [hn1]
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s14 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc9; omega
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
                have hw := gallai_int G
                try push_cast at hw
                linarith [hw]
              have s16 : (G.indepNum : ℤ) ≥ 2 := by linarith [s14, s12, s15]
              have s17 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s18 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by linarith [s10, s11, s12, s17, s15]
              linarith [s18]
            · -- 1*n <= 2
              have s19 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
                have hw := max_lt_card_int' G
                try push_cast at hw
                linarith [hw]
              have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s22 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc9; omega
              have s23 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s24 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
              have s25 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s23]) (by linarith [s24])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s26 : -4 * (G.maxDegree : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 9 := by linarith [s19, s20, s21, s22, s25]
              have s27 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s26; omega
              linarith [s27]
          linarith [s9]
      linarith [s2]
    · -- 1*max_deg <= 0
      have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s29 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s30 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s31 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by linarith [s28, s29, s30]
      linarith [s31]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

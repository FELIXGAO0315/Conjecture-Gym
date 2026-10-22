import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C248 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.edgeFinset.card : ℤ)) :
    2 * (G.edgeFinset.card : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 9 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
        by_cases hc7 : (1 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 1
          have s8 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
            by_cases hc8 : (2 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 2
              have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s11 : (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
              have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s13 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc8; omega
              have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s13]) (by linarith [s12])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s15 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s9, s10, s11, s14]
              linarith [s15]
            · -- 1*alpha <= 1
              have s16 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc7; omega
              have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s18 : (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
              have s19 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc8; omega
              have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s21 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s19]) (by linarith [s20])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s22 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s16, s17, s18, s19, s21]
              linarith [s22]
          linarith [s8]
        · -- 1*m <= 0
          have s23 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s24 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : -(G.edgeFinset.card : ℤ) ≥ 0 := by have hcc := hc7; omega
          have s26 : -2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s23, s24, s25]
          linarith [s26]
      linarith [s7]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

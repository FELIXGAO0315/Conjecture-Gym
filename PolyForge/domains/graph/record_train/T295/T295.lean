import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T295 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 12 := by
  have s1 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
        by_cases hc8 : (1 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 1
          have s9 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
            by_cases hc9 : (3 : ℤ) ≤ (G.indepNum : ℤ)
            · -- 1*alpha >= 3
              have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s11 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc9; omega
              have s12 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc8; omega
              have s13 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s10, s11, s12]
              linarith [s13]
            · -- 1*alpha <= 2
              have s14 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s16 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc9; omega
              have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s18 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s16]) (by linarith [s17])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s19 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s14, s15, s16, s18]
              have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s19; omega
              have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
              have s22 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s23 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s22]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s24 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s14, s15, s21, s23]
              have s25 : (G.indepNum : ℤ) ≥ 2 := by have hr := s24; omega
              have s26 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc8; omega
              have s27 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s20, s25, s26]
              linarith [s27]
          linarith [s9]
        · -- 1*m <= 0
          have s28 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s29 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
          have s30 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s31 : -(G.edgeFinset.card : ℤ) ≥ 0 := by have hcc := hc8; omega
          have s32 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s33 : (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s28, s29, s30, s31, s32]
          linarith [s33]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

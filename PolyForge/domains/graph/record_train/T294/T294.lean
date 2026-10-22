import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T294 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 11 := by
  have s1 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
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
      have s7 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
        by_cases hc8 : (1 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 1
          have s9 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by
            by_cases hc9 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 2
              have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc9; omega
              have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc9; omega
              have s14 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s14]) (by linarith [s13])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s16 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s11, s12, s13, s15]
              have s17 : (G.indepNum : ℤ) ≥ 2 := by have hr := s16; omega
              have s18 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc8; omega
              have s19 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s10, s17, s18]
              linarith [s19]
            · -- 1*chi <= 1
              have s20 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
              have s21 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc8; omega
              have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s23 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc9; omega
              have s24 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s25 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
                  mul_nonneg (by linarith [s24]) (by linarith [s23])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s26 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s20, s21, s22, s23, s25]
              linarith [s26]
          linarith [s9]
        · -- 1*m <= 0
          have s27 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s28 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
          have s29 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(G.edgeFinset.card : ℤ) ≥ 0 := by have hcc := hc8; omega
          have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s32 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 11 := by linarith [s27, s28, s29, s30, s31]
          linarith [s32]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

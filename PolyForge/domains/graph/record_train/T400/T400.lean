import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T400 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2) :
    (G.maxDegree : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 6 := by
  have s1 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.edgeFinset.card : ℤ)
    · -- 1*m >= 1
      have s2 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
        by_cases hc2 : (2 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 2
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s4 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc2; omega
          have s5 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s6 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s3, s4, s5]
          linarith [s6]
        · -- 1*alpha <= 1
          have s7 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
            by_cases hc7 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
            · -- 1*chi >= 3
              have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc7; omega
              have s9 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s10 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s11 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s8, s9, s10]
              linarith [s11]
            · -- 1*chi <= 2
              have s12 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn1]
              have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
                have hw := card_le_alpha_chi_int G
                try push_cast at hw
                linarith [hw]
              have s14 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc2; omega
              have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s16 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
                  mul_nonneg (by linarith [s14]) (by linarith [s15])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s12, s13, s14, s16]
              have s18 : (G.indepNum : ℤ) ≥ 1 := by
                have hw := alpha_ge_one_int' G
                try push_cast at hw
                linarith [hw]
              have s19 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc1; omega
              have s20 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hw := handshake_max_int G
                try push_cast at hw
                linarith [hw]
              have s21 : (G.maxDegree : ℤ) ≥ 0 := by positivity
              have s22 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc7; omega
              have s23 : -(Fintype.card V : ℤ) ≥ -2 := by linarith [s13, s14, s22, s16]
              have s24 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
                have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
                  mul_nonneg (by linarith [s23]) (by linarith [s21])
                ring_nf at hmul ⊢
                linarith [hmul]
              have s25 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s17, s18, s19, s20, s24]
              linarith [s25]
          linarith [s7]
      linarith [s2]
    · -- 1*m <= 0
      have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s27 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn1]
      have s28 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s29 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s30 : -(G.edgeFinset.card : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s32 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by linarith [s26, s27, s28, s29, s30, s31]
      linarith [s32]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

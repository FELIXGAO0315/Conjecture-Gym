import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C198 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ (G.cliqueNum : ℤ)) (hn2 : (Fintype.card V : ℤ) ≥ 6) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.maxDegree : ℤ) + 12 := by
  have s1 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*omega <= 2
      have s6 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
        by_cases hc6 : (6 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 6
          have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 6 := by have hcc := hc6; omega
          have s8 : (G.maxDegree : ℤ) ≥ 0 := by positivity
          have s9 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s7, s8]
          linarith [s9]
        · -- 1*chi <= 5
          have s10 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn2]
          have s11 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s12 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
            have hw := handshake_max_int G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
          have s14 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s15 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s13, s14]
          have s16 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by have hcc := hc6; omega
          have s19 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s20 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : -(G.maxDegree : ℤ) ≥ -9 := by linarith [s16, s17, s13, s14, s18, s20]
          have s22 : 9 * (Fintype.card V : ℤ) + 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 54 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * (9 - (G.maxDegree : ℤ)) :=
              mul_nonneg (by linarith [s10]) (by linarith [s21])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s17, s13, s14, s18, s20]
          have s24 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
            have hw := omega_le_maxdeg_add_one_int G
            try push_cast at hw
            linarith [hw]
          have s25 : 5 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s10, s24, s17, s13, s18, s20]
          have s26 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s25; omega
          have s27 : (Fintype.card V : ℤ) + 10 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 10 := by
            have hmul : (0 : ℤ) ≤ (10 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s23]) (by linarith [s26])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s29 : 19 * (G.maxDegree : ℤ) ≥ 23 := by linarith [s11, s12, s15, s22, s27, s28]
          have s30 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s29; omega
          have s31 : 5 * (G.indepNum : ℤ) ≥ 6 := by linarith [s10, s17, s18, s20]
          have s32 : (G.indepNum : ℤ) ≥ 2 := by have hr := s31; omega
          have s33 : 2 * (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 10 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s32]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by linarith [s10, s30, s17, s15, s33]
          linarith [s34]
      linarith [s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

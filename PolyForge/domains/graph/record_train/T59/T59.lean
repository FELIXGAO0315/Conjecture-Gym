import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T59 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) :
    2 * (Fintype.card V : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 12 := by
  have s1 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by
        by_cases hc7 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s9 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc7; omega
          have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s12 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by linarith [s8, s9, s10, s11]
          linarith [s12]
        · -- 1*alpha <= 2
          have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s15 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc7; omega
          have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s17 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s15]) (by linarith [s16])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s18 : (G.maxDegree : ℤ) = 2 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s19 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s13, s14, s15, s17, s18]
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
          have s24 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s13, s14, s21, s23, s18]
          have s25 : (G.indepNum : ℤ) ≥ 2 := by have hr := s24; omega
          have s26 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s27 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s26, s21]
          have s28 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s27])
            try push_cast at hw
            linarith [hw]
          have s29 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s13, s18]
          have s30 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s14, s21, s15, s17]
          have s31 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s29]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s33 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 16 := by linarith [s20, s25, s28, s31, s32]
          linarith [s33]
      linarith [s7]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

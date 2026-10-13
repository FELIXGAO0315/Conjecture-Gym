import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C56 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 5) :
    (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 9 := by
  have s1 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by
        by_cases hc2 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 3
          have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s5 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s7 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s3, s4, s5, s6]
          linarith [s7]
        · -- 1*chi <= 2
          have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc2; omega
          have s11 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s8]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s12 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s8, s9, s11]
          linarith [s12]
      linarith [s2]
    · -- 1*alpha <= 2
      have s13 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by
        by_cases hc13 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
        · -- 1*omega >= 3
          have s14 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc13; omega
          have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s14, s15]
          have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s18 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s19 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
              mul_nonneg (by linarith [s18]) (by linarith [s16])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s20 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s16, s17, s19]
          linarith [s20]
        · -- 1*omega <= 2
          have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s22 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc13; omega
          have s23 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
            have hw := turan_r2_int G (by linarith [s22])
            try push_cast at hw
            linarith [hw]
          have s24 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s25 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s26 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s24, s25]
          have s27 : -(G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [hn1]
          have s28 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s29 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s30 : -(Fintype.card V : ℤ) ≥ -7 := by linarith [s27, s28, s29]
          have s31 : 11 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 28 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (7 - (Fintype.card V : ℤ)) :=
              mul_nonneg (by linarith [s26]) (by linarith [s30])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s32 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s33 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s28]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s34 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s24, s21, s28, s33, s25]
          have s35 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
              mul_nonneg (by linarith [s28]) (by linarith [s34])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s36 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s37 : -5 * (Fintype.card V : ℤ) + 15 * (G.chromaticNumber.toNat : ℤ) + 15 * (G.indepNum : ℤ) ≥ 44 := by linarith [s21, s23, s31, s35, s36]
          have s38 : -(Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by have hr := s37; omega
          linarith [s38]
      linarith [s13]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

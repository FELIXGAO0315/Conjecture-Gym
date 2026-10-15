import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C276 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    4 * (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) + 5 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by
        by_cases hc2 : (4 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 4
          have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s4 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
          have s5 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s6 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := chi_le_n_int G
            try push_cast at hw
            linarith [hw]
          have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [s6, s4]
          have s8 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s5]) (by linarith [s7])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hcc := hc2; omega
          have s10 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
          have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s12 : -(G.indepNum : ℤ) ≥ -5 := by linarith [s10, s4, s11]
          have s13 : 5 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 20 := by
            have hmul : (0 : ℤ) ≤ (5 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 4) :=
              mul_nonneg (by linarith [s12]) (by linarith [s9])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s14 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s15 : -7 * (G.edgeFinset.card : ℤ) + 21 * (G.chromaticNumber.toNat : ℤ) - 21 * (G.vertexCoverNum.toNat : ℤ) ≥ -30 := by linarith [s3, s4, s8, s13, s11, s14]
          have s16 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by have hr := s15; omega
          linarith [s16]
        · -- 1*chi <= 3
          have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc2; omega
          have s18 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hcc := hc2; omega
          have s21 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s21]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s24 : -3 * (G.vertexCoverNum.toNat : ℤ) ≥ -10 := by linarith [s19, s18, s20, s22, s23]
          have s25 : -(G.vertexCoverNum.toNat : ℤ) ≥ -3 := by have hr := s24; omega
          have s26 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s27 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s17, s18, s25, s26]
          linarith [s27]
      linarith [s2]
    · -- 1*chi <= 2
      have s28 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by
        by_cases hc28 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s29 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc28; omega
          have s30 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
          have s31 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s32 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc28; omega
          have s33 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s34 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s33]) (by linarith [s32])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s35 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s36 : -2 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s31, s30, s32, s34, s35]
          have s37 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hr := s36; omega
          have s38 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s39 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s29, s30, s37, s38]
          linarith [s39]
        · -- 1*chi <= 1
          have s40 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s41 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
          have s42 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s43 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc28; omega
          have s44 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s42]) (by linarith [s43])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s45 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s46 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
            have hw := regular_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s47 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [s40, s41, s44, s45, s46]
          linarith [s47]
      linarith [s28]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

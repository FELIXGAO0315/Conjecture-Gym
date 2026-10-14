import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C206 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.indepNum : ℤ) ≤ 4) :
    (Fintype.card V : ℤ) ≤ 4 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - 14 := by
  have s1 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn1]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : 4 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
        have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
          mul_nonneg (by linarith [s4]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s9 : 2 * (G.edgeFinset.card : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 13 := by linarith [s2, s3, s6, s7, s8]
      have s10 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by have hr := s9; omega
      linarith [s10]
    · -- 1*chi <= 2
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s12, s13]
      have s15 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s14])
        try push_cast at hw
        linarith [hw]
      have s16 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s16, s17]
      have s19 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn1]
      have s20 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s19]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s11, s19, s13, s21]
      have s23 : 12 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 32 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (8 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s18]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s25 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s24]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s26 : (G.indepNum : ℤ) ≥ 2 := by linarith [s16, s11, s13, s25, s17]
      have s27 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s26]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s28 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s29 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s30 : 3 * (G.edgeFinset.card : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ 20 := by linarith [s11, s15, s23, s27, s28, s29]
      have s31 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by have hr := s30; omega
      linarith [s31]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

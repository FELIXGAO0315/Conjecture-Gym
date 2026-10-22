import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C31 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 4) :
    (Fintype.card V : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) + 12 := by
  have s1 : (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 21 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : 2 * (G.edgeFinset.card : ℤ) ≥ 15 := by linarith [s3, s4, s5, s6]
      have s8 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hr := s7; omega
      have s9 : 3 * (Fintype.card V : ℤ) ≥ 16 := by linarith [s8, s6]
      have s10 : (Fintype.card V : ℤ) ≥ 6 := by have hr := s9; omega
      have s11 : (G.minDegree : ℤ) = 3 := by
        have hw := regular_min_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 21 := by linarith [s2, s10, s11, s6]
      linarith [s12]
    · -- 1*chi <= 2
      have s13 : (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [hn1]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.indepNum : ℤ) ≥ 4 := by linarith [s13, s14, s15, s17, s18]
      have s20 : 4 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 4) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s19]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : (G.minDegree : ℤ) = 3 := by
        have hw := regular_min_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s22 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s23 : (G.edgeFinset.card : ℤ) + (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 21 := by linarith [s19, s13, s14, s20, s18, s21, s22]
      linarith [s23]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

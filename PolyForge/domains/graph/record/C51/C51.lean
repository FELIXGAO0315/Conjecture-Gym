import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C51 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) :
    (G.chromaticNumber.toNat : ℤ) ≥ -2 * (G.indepNum : ℤ) + 5 := by
  have s1 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s5 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s9]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s12 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s6, s7, s8, s10, s11]
      have s13 : (G.indepNum : ℤ) ≥ 2 := by have hr := s12; omega
      have s14 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s6, s11]
      have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s17 : 4 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 4 * (G.vertexCoverNum.toNat : ℤ) ≥ 11 := by linarith [s13, s14, s7, s15, s16]
      have s18 : 2 * (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by have hr := s17; omega
      linarith [s18]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

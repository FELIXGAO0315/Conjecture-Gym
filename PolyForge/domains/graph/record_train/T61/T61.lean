import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T61 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) :
    (Fintype.card V : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) - (G.indepNum : ℤ) + 7 := by
  have s1 : (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 7 := by
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
      have s6 : (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 7 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 2
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s9 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s10 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s7, s8, s9]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s7, s11, s12, s14, s8]
      have s16 : (G.indepNum : ℤ) ≥ 2 := by have hr := s15; omega
      have s17 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : 2 * (Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 13 := by linarith [s10, s11, s17, s9]
      have s19 : (Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 7 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C300 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.indepNum : ℤ) ≤ 5) :
    2 * (G.indepNum : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) + 10 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 11 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s7 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s5, s6]
      have s8 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s7])
        try push_cast at hw
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s9, s10]
      have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.indepNum : ℤ) ≥ -5 := by linarith [hn1]
      have s14 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s12, s13, s6, s15]
      have s17 : 13 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 30 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (10 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s19 : 3 * (Fintype.card V : ℤ) ≥ 10 := by linarith [s8, s17, s18]
      have s20 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s19; omega
      have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s22 : 5 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ (5 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s13]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s23 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s9, s12, s6, s15, s10]
      have s24 : (G.indepNum : ℤ) ≥ 2 := by have hr := s23; omega
      have s25 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s24]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s26 : 12 * (G.chromaticNumber.toNat : ℤ) + 8 * (G.indepNum : ℤ) ≥ 37 := by linarith [s20, s12, s22, s25]
      have s27 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 10 := by have hr := s26; omega
      linarith [s27]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

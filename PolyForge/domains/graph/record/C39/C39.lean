import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C39 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.indepNum : ℤ) ≤ 4) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 9 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 9 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s8 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s8]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s11 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s5, s6, s7, s9, s10]
      have s12 : (G.indepNum : ℤ) ≥ 2 := by have hr := s11; omega
      have s13 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s13, s7]
      have s15 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s14])
        try push_cast at hw
        linarith [hw]
      have s16 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s10]
      have s17 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn1]
      have s18 : -(Fintype.card V : ℤ) ≥ -8 := by linarith [s6, s17, s7, s9]
      have s19 : 11 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 24 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (8 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s22 : 14 * (G.chromaticNumber.toNat : ℤ) + 21 * (G.indepNum : ℤ) ≥ 66 := by linarith [s12, s6, s15, s19, s20, s21]
      have s23 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by have hr := s22; omega
      linarith [s23]
  linarith [s1]

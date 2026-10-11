import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C55 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.indepNum : ℤ) ≤ 5) :
    (Fintype.card V : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) + 14 := by
  have s1 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 14 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 14 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s8 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s6, s7]
      have s9 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s8])
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s10, s11]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.indepNum : ℤ) ≥ -5 := by linarith [hn1]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) ≥ -10 := by linarith [s13, s14, s7, s16]
      have s18 : 13 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 30 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (10 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s17])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s20 : 3 * (Fintype.card V : ℤ) ≥ 10 := by linarith [s9, s18, s19]
      have s21 : (Fintype.card V : ℤ) ≥ 4 := by have hr := s20; omega
      have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s23 : 5 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ (5 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s14]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s24 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s10, s13, s7, s16, s11]
      have s25 : (G.indepNum : ℤ) ≥ 2 := by have hr := s24; omega
      have s26 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s25]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s27 : 4 * (Fintype.card V : ℤ) + 12 * (G.chromaticNumber.toNat : ℤ) + 8 * (G.indepNum : ℤ) ≥ 53 := by linarith [s21, s13, s23, s26]
      have s28 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 14 := by have hr := s27; omega
      linarith [s28]
  linarith [s1]

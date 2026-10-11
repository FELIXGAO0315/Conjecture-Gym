import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2) (hn2 : (G.indepNum : ℤ) ≤ 2) :
    (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 3
      have s2 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s4]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s8 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s6, s7]
      have s9 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r2_int G (by linarith [s8])
        try push_cast at hw
        linarith [hw]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.indepNum : ℤ) ≥ -2 := by linarith [hn2]
      have s12 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s11]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s10, s7, s11, s13]
      have s15 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 12 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (4 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s4]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s16, s17, s10, s7, s11, s13]
      have s19 : -3 * (Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -12 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * (3 - (G.minDegree : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 25 * (G.edgeFinset.card : ℤ) - 75 * (G.minDegree : ℤ) ≥ -72 := by linarith [s2, s5, s9, s15, s19]
      have s21 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by have hr := s20; omega
      linarith [s21]
    · -- 1*n <= 2
      have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s23 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s24 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s25 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s26 : (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ -2 := by linarith [s22, s23, s24, s25]
      linarith [s26]
  linarith [s1]

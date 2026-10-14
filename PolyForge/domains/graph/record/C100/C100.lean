import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C100 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≥ 3 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 5
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc1; omega
      have s8 : -5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -5 * (G.minDegree : ℤ) ≥ -12 := by linarith [s4, s5, s8]
      have s10 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s9; omega
      have s11 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s2, s3, s10]
      linarith [s11]
    · -- 1*n <= 4
      have s12 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc1; omega
      have s16 : -(G.minDegree : ℤ) ≥ -3 := by linarith [s12, s13, s15]
      have s17 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s18 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -4 := by linarith [s18, s15]
      have s20 : (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (4 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s22 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 0 := by
        have hw := alpha_le_card_int G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.indepNum : ℤ) ≥ -4 := by linarith [s22, s15]
      have s24 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s23]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s25 : -15 * (G.minDegree : ℤ) + 5 * (G.chromaticNumber.toNat : ℤ) + 15 * (G.indepNum : ℤ) ≥ -13 := by linarith [s12, s13, s14, s16, s20, s24]
      have s26 : -3 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by have hr := s25; omega
      linarith [s26]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

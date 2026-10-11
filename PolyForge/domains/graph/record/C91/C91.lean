import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C91 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.IsRegularOfDegree 3) (hn1 : (G.girth : ℤ) ≤ (G.vertexCoverNum.toNat : ℤ)) :
    (G.maxDegree : ℤ) ≥ -3 * (G.edgeFinset.card : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 33 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 33 := by
    by_cases hc1 : (6 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 6
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) ≥ 6 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp2
        try push_cast at hw
        linarith [hw]
      have s5 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s6 : 3 * (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 33 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*n <= 5
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp2
        try push_cast at hw
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s7, s8]
      have s10 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s11 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [s7, s8, s10]
      have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.girth : ℤ) ≥ 3 := by
        have hw := girth_ge_three_int G hp1
        try push_cast at hw
        linarith [hw]
      have s14 : (G.vertexCoverNum.toNat : ℤ) - (G.girth : ℤ) ≥ 0 := by linarith [hn1]
      have s15 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s13, s14]
      have s16 : -(Fintype.card V : ℤ) ≥ -5 := by have hcc := hc1; omega
      have s17 : -2 * (G.edgeFinset.card : ℤ) ≥ -15 := by linarith [s16, s10]
      have s18 : -(G.edgeFinset.card : ℤ) ≥ -7 := by have hr := s17; omega
      have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s20 : -3 * (G.indepNum : ℤ) ≥ -5 := by linarith [s15, s18, s19, s10]
      have s21 : -(G.indepNum : ℤ) ≥ -1 := by have hr := s20; omega
      have s22 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.indepNum : ℤ) ≥ -2 := by linarith [s13, s14, s16, s19]
      have s24 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s23]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s25 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s15, s12, s24, s19]
      have s26 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s25; omega
      have s27 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 3) :=
          mul_nonneg (by linarith [s21]) (by linarith [s26])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s28 : 3 * (G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 33 := by linarith [s9, s11, s12, s21, s27, s8]
      linarith [s28]
  linarith [s1]

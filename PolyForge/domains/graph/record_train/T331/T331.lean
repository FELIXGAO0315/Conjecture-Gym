import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T331 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) (hn2 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + (G.indepNum : ℤ) := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s9 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s5]
      have s10 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s9]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 0 := by linarith [s2, s3, s4, s5, s6, s7, s10, s11]
      linarith [s12]
    · -- 1*chi <= 2
      have s13 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn2]
      have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s20 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s21 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s20]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : 2 * (G.edgeFinset.card : ℤ) - 4 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ -1 := by linarith [s13, s14, s15, s16, s17, s18, s19, s21]
      have s23 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + (G.indepNum : ℤ) ≥ 0 := by have hr := s22; omega
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

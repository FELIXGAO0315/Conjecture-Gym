import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T329 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2) :
    2 * (G.minDegree : ℤ) ≤ (G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s3]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s7 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ -1 := by linarith [s2, s7, s8, s3, s6, s9]
      have s11 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s4]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by linarith [s4, s5, s6, s10, s12, s9]
      linarith [s13]
    · -- 1*chi <= 2
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
      have s17 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s20 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by linarith [s14, s15, s16, s17, s18, s19, s20]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

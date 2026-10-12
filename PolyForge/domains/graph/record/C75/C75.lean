import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C75 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 1) (hn2 : (G.chromaticNumber.toNat : ℤ) ≥ (Fintype.card V : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ -3 * (G.maxDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 8 := by
  have s1 : (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s6 : -(Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : -(G.indepNum : ℤ) ≥ -1 := by
        have hw := complete_indep_le_one_int G (by linarith [s6])
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by linarith [s2, s3, s4, s5, s7, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [hn1]
      have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s13 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s14 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : -(G.maxDegree : ℤ) ≥ -1 := by linarith [s14, s12, s15]
      have s17 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s19 : -(Fintype.card V : ℤ) ≥ -2 := by linarith [s12, s15]
      have s20 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s19]) (by linarith [s18])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : (G.edgeFinset.card : ℤ) + 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 8 := by linarith [s10, s11, s12, s17, s20]
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

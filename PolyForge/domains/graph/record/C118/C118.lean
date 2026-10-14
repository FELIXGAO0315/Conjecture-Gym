import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C118 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) + 6 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s5 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s3, s4]
      have s6 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s7 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s9 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s5]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s11 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 9 * (G.indepNum : ℤ) ≥ 19 := by linarith [s2, s5, s6, s7, s9, s10]
      have s12 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 7 := by have hr := s11; omega
      linarith [s12]
    · -- 1*chi <= 2
      have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (Fintype.card V : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s16 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s18 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s16]) (by linarith [s17])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s13, s14, s15, s18]
      have s20 : (G.indepNum : ℤ) ≥ 2 := by have hr := s19; omega
      have s21 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s22 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s23 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s13, s15]
      have s24 : -2 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s23]) (by linarith [s22])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s25 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s20, s21, s24]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

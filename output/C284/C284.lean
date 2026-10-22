import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C284 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.vertexCoverNum.toNat : ℤ) ≥ 1) :
    (G.chromaticNumber.toNat : ℤ) ≥ -(G.maxDegree : ℤ) + 3 := by
  have s1 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s4 : 2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by linarith [hn2]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s8 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s8]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s12 : 3 * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by linarith [s5, s6, s7, s10, s11]
      have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s12; omega
      have s14 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s14, s5]
      have s16 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s18 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s7, s9]
      have s19 : 4 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (4 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s18]) (by linarith [s17])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s13, s15, s16, s19]
      have s21 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hr := s20; omega
      linarith [s21]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

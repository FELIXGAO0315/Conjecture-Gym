import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C20 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) + (G.vertexCoverNum.toNat : ℤ) + 2 := by
  have s1 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn1]
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
      have s12 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s5, s6, s7, s10, s11]
      have s13 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by have hr := s12; omega
      linarith [s13]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

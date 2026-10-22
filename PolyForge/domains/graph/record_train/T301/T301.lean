import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T301 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 3) :
    (G.edgeFinset.card : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) + 7 := by
  have s1 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
      have s5 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [hn1]
      have s9 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s8, s10, s11, s13]
      have s15 : (G.indepNum : ℤ) ≥ 2 := by have hr := s14; omega
      have s16 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s18 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 13 := by linarith [s8, s9, s10, s16, s17]
      have s19 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 7 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T192 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    (G.edgeFinset.card : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) + 8 := by
  have s1 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.edgeFinset.card : ℤ) ≥ 3 := by
        have hw := three_le_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s5 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s9]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s6, s7, s8, s10]
      have s12 : (G.indepNum : ℤ) ≥ 2 := by have hr := s11; omega
      have s13 : (G.edgeFinset.card : ℤ) ≥ 3 := by
        have hw := three_le_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s14 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : 2 * (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 17 := by linarith [s12, s6, s13, s7, s14]
      have s16 : (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 9 := by have hr := s15; omega
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T188 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    (G.edgeFinset.card : ℤ) ≥ -2 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 12 := by
  have s1 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by
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
      have s5 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 12 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
        by_cases hc6 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc6; omega
          have s8 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc6; omega
          have s11 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s12 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s11]) (by linarith [s10])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s13 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s8, s9, s10, s12]
          have s14 : (G.indepNum : ℤ) ≥ 2 := by have hr := s13; omega
          have s15 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s16 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by linarith [s7, s14, s15]
          linarith [s16]
        · -- 1*chi <= 1
          have s17 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s18 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s19 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s20 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc6; omega
          have s21 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s22 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s21]) (by linarith [s20])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s23 : (G.edgeFinset.card : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 14 := by linarith [s17, s18, s19, s20, s22]
          linarith [s23]
      linarith [s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T191 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    2 * (G.edgeFinset.card : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.indepNum : ℤ) + 18 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 18 := by
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
      have s5 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 18 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 18 := by
        by_cases hc6 : (3 : ℤ) ≤ (G.indepNum : ℤ)
        · -- 1*alpha >= 3
          have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s8 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc6; omega
          have s9 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s10 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 18 := by linarith [s7, s8, s9]
          linarith [s10]
        · -- 1*alpha <= 2
          have s11 : (Fintype.card V : ℤ) ≥ 3 := by
            have hw := three_le_card_of_cycle_int G hp1
            try push_cast at hw
            linarith [hw]
          have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s13 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc6; omega
          have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s13]) (by linarith [s14])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s11, s12, s13, s15]
          have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s16; omega
          have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s19 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s20 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s19]) (by linarith [s18])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s11, s12, s18, s20]
          have s22 : (G.indepNum : ℤ) ≥ 2 := by have hr := s21; omega
          have s23 : (G.edgeFinset.card : ℤ) ≥ 3 := by
            have hw := three_le_edges_int G hp1
            try push_cast at hw
            linarith [hw]
          have s24 : 2 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 18 := by linarith [s17, s22, s23]
          linarith [s24]
      linarith [s6]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

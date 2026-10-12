import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C80 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) :
    2 * (G.indepNum : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) + 5 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (Fintype.card V : ℤ) ≥ 3 := by
        have hw := three_le_card_of_cycle_int G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s8 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s8]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s5, s6, s7, s9]
      have s11 : (G.indepNum : ℤ) ≥ 2 := by have hr := s10; omega
      have s12 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 11 := by linarith [s11, s5, s6, s12]
      have s14 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by have hr := s13; omega
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

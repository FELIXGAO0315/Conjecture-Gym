import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C52 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) (hn2 : (Fintype.card V : ℤ) ≥ 4) :
    2 * (G.indepNum : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) + 6 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
      have s7 : (G.chromaticNumber.toNat : ℤ) + 5 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (5 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s5]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : 5 * (G.chromaticNumber.toNat : ℤ) + 10 * (G.indepNum : ℤ) ≥ 27 := by linarith [s2, s3, s4, s7]
      have s9 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by have hr := s8; omega
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (Fintype.card V : ℤ) ≥ 4 := by linarith [hn2]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s10, s11, s14]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

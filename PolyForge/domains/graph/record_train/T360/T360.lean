import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T360 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ (G.indepNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≥ (Fintype.card V : ℤ) - 4 * (G.indepNum : ℤ) + 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s3, s2, s4, s5]
      have s7 : (G.indepNum : ℤ) ≥ 2 := by have hr := s6; omega
      have s8 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s2, s7, s4]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s9]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s9, s10, s12, s13]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

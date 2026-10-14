import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C107 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.indepNum : ℤ) ≤ 3) (hn2 : (Fintype.card V : ℤ) ≥ 2) :
    2 * (G.indepNum : ℤ) ≥ (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 5 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 2
      have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : -(G.indepNum : ℤ) ≥ -3 := by linarith [hn1]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ (3 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
          mul_nonneg (by linarith [s3]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by linarith [s2, s5, s6]
      linarith [s7]
    · -- 1*chi <= 1
      have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) ≥ 2 := by linarith [hn2]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s13 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s15 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 5 := by linarith [s8, s9, s10, s13, s14]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

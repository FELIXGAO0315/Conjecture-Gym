import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C75 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 6) :
    (G.minDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.vertexCoverNum.toNat : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5, s6, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 6 := by linarith [s9, s10, s11, s12, s13, s16, s17]
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

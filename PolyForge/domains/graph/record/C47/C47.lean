import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C47 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s4]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by linarith [s2, s3, s4, s5, s7]
      linarith [s8]
    · -- 1*alpha <= 1
      have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s11 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s12 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s13]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 8 := by linarith [s9, s10, s11, s12, s15]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

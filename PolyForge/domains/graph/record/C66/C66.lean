import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C66 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≤ 6) :
    (G.diam : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -(G.diam : ℤ) ≥ -6 := by linarith [hn1]
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 6 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s8 : (G.diam : ℤ) ≥ 0 := by positivity
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s10]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.diam : ℤ) ≥ 6 := by linarith [s6, s7, s8, s9, s12]
      linarith [s13]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

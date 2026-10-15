import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C272 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 6) (hn2 : (G.radius.toNat : ℤ) ≤ 3) :
    (G.radius.toNat : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 4 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.radius.toNat : ℤ) ≥ -3 := by linarith [hn2]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s8 : 2 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 12 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5, s8]
      linarith [s9]
    · -- 1*alpha <= 1
      have s10 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s12 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s14 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [hn1]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s14]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 4 := by linarith [s10, s11, s12, s13, s16]
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

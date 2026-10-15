import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C301 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2) :
    2 * (G.radius.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) + 3 := by
  have s1 : 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.radius.toNat : ℤ)
    · -- 1*radius >= 1
      have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : (G.radius.toNat : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [hn1]
      have s7 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 6 * (G.indepNum : ℤ) - 4 * (G.diam : ℤ) + 4 * (G.radius.toNat : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5, s6, s8]
      have s10 : 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by have hr := s9; omega
      linarith [s10]
    · -- 1*radius <= 0
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp1
        try push_cast at hw
        linarith [hw]
      have s13 : -(G.radius.toNat : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s14 : 3 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s11, s12, s13]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

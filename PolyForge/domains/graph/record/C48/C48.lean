import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C48 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsAcyclic) (hn1 : (G.maxDegree : ℤ) ≤ 2 * (G.minDegree : ℤ)) :
    2 * (G.minDegree : ℤ) ≥ 2 * (G.maxDegree : ℤ) - 3 * (G.indepNum : ℤ) + 3 := by
  have s1 : -2 * (G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (1 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 1
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : (G.minDegree : ℤ) ≥ 1 := by have hcc := hc1; omega
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
      have s7 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -4 * (G.maxDegree : ℤ) + 4 * (G.minDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5, s6, s8]
      have s10 : -2 * (G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by have hr := s9; omega
      linarith [s10]
    · -- 1*min_deg <= 0
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
      have s13 : -(G.minDegree : ℤ) ≥ 0 := by have hcc := hc1; omega
      have s14 : -2 * (G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s11, s12, s13]
      linarith [s14]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

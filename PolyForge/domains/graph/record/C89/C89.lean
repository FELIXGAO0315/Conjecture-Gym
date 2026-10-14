import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C89 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≥ 2) (hn2 : (G.indepNum : ℤ) ≤ 4) :
    2 * (Fintype.card V : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) := by
  have s1 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
      have s5 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn2]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*chi <= 2
      have s8 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        by_cases hc8 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc8; omega
          have s10 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
            have hw := tau_le_edges_int G
            try push_cast at hw
            linarith [hw]
          have s11 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
          have s12 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn2]
          have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s14 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s9, s10, s11, s12, s13]
          linarith [s14]
        · -- 1*chi <= 1
          have s15 : (G.edgeFinset.card : ℤ) ≥ 2 := by linarith [hn1]
          have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s17 : -(G.indepNum : ℤ) ≥ -4 := by linarith [hn2]
          have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc8; omega
          have s19 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s20 : 4 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
            have hmul : (0 : ℤ) ≤ (4 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
              mul_nonneg (by linarith [s17]) (by linarith [s19])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s21 : -2 * (Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s15, s16, s17, s18, s20]
          linarith [s21]
      linarith [s8]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

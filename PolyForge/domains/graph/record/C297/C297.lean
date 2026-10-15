import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C297 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    2 * (G.indepNum : ℤ) ≥ (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 6 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*omega <= 2
      have s7 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by
        by_cases hc7 : (2 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
        · -- 1*chi >= 2
          have s8 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hcc := hc7; omega
          have s9 : -(Fintype.card V : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
          have s10 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s11 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 6 := by linarith [s8, s9, s10]
          linarith [s11]
        · -- 1*chi <= 1
          have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
            have hw := card_le_alpha_chi_int G
            try push_cast at hw
            linarith [hw]
          have s15 : (G.indepNum : ℤ) ≥ 1 := by
            have hw := alpha_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s16 : -(G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hcc := hc7; omega
          have s17 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (1 - (G.chromaticNumber.toNat : ℤ)) :=
              mul_nonneg (by linarith [s15]) (by linarith [s16])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s18 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
            have hw := gallai_int G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.maxDegree : ℤ) = 3 := by
            have hw := regular_max_int' G hp1
            try push_cast at hw
            linarith [hw]
          have s20 : 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s12, s13, s14, s17, s18, s19]
          linarith [s20]
      linarith [s7]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

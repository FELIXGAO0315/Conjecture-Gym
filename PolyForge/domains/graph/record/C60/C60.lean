import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C60 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≥ 2) (hn2 : (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ)) :
    (G.maxDegree : ℤ) ≥ 3 * (G.minDegree : ℤ) - 3 * (G.indepNum : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 3
      have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 0 := by linarith [hn2]
      have s7 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s7]) (by linarith [s2])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s10 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s10, s3]
      have s12 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s6, s8, s12]
      linarith [s13]
    · -- 1*max_deg <= 2
      have s14 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s16 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn1]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s18 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s18]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s14, s15, s16, s17, s19]
      have s21 : (G.indepNum : ℤ) ≥ 2 := by have hr := s20; omega
      have s22 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.maxDegree : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s24 : -(G.minDegree : ℤ) ≥ -2 := by linarith [s22, s23]
      have s25 : (G.maxDegree : ℤ) - 3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by linarith [s21, s16, s24]
      linarith [s25]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]

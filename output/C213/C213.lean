import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C213 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 3) (hp2 : ¬ G.IsBipartite) (hn1 : (G.indepNum : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (Fintype.card V : ℤ) ≥ -3 * (G.chromaticNumber.toNat : ℤ) - (G.indepNum : ℤ) + 17 := by
  have s1 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 17 := by
    by_cases hc1 : (4 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 4
      have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 4 := by have hcc := hc1; omega
      have s4 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 17 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*chi <= 3
      have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hw := not_bipartite_chi_int G hp2
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s11 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s11]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : (G.maxDegree : ℤ) = 3 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s14 : 3 * (G.indepNum : ℤ) ≥ 4 := by linarith [s8, s9, s10, s12, s13]
      have s15 : (G.indepNum : ℤ) ≥ 2 := by have hr := s14; omega
      have s16 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s17 : -(G.cliqueNum : ℤ) ≥ -3 := by linarith [s16, s10]
      have s18 : -6 * (G.edgeFinset.card : ℤ) + 2 * (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := turan_r3_int G (by linarith [s17])
        try push_cast at hw
        linarith [hw]
      have s19 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s8, s13]
      have s20 : 2 * (G.cliqueNum : ℤ) - (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
      have s21 : -(Fintype.card V : ℤ) ≥ -18 := by linarith [s16, s9, s20, s10, s12]
      have s22 : 22 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 72 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * (18 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s19]) (by linarith [s21])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s23 : -3 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s24 : 35 * (Fintype.card V : ℤ) ≥ 144 := by linarith [s18, s22, s23]
      have s25 : (Fintype.card V : ℤ) ≥ 5 := by have hr := s24; omega
      have s26 : 2 * (G.edgeFinset.card : ℤ) ≥ 15 := by linarith [s25, s23]
      have s27 : (G.edgeFinset.card : ℤ) ≥ 8 := by have hr := s26; omega
      have s28 : 3 * (Fintype.card V : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 49 := by linarith [s7, s15, s27, s23]
      have s29 : (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 17 := by have hr := s28; omega
      linarith [s29]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

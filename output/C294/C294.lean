import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C294 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hp2 : G.IsBipartite) :
    2 * (G.indepNum : ℤ) ≥ (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) + 6 := by
  have s1 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp2
        try push_cast at hw
        linarith [hw]
      have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s4]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s6 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by linarith [s2, s5, s6]
      linarith [s7]
    · -- 1*alpha <= 2
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp2
        try push_cast at hw
        linarith [hw]
      have s12 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s10]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s14]) (by linarith [s13])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s17 : -2 * (Fintype.card V : ℤ) + 2 * (G.edgeFinset.card : ℤ) = 0 := by
        have hw := regular_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s18 : -3 * (G.edgeFinset.card : ℤ) + 9 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 16 := by linarith [s8, s9, s12, s15, s16, s17]
      have s19 : -(G.edgeFinset.card : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 6 := by have hr := s18; omega
      linarith [s19]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]

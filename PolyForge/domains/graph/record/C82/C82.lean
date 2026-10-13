import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C82 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hp2 : 2 ≤ Fintype.card V) :
    (G.radius.toNat : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s6 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s7 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s6]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by linarith [s2, s3, s4, s7]
      linarith [s8]
    · -- 1*alpha <= 1
      have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s12 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G (isTree_connected G hp1) hp2
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s17 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s16]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s19 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.radius.toNat : ℤ) ≥ 5 := by linarith [s9, s10, s11, s12, s13, s14, s17, s18]
      linarith [s19]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

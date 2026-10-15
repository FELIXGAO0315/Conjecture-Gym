import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C32 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) (hn2 : (G.diam : ℤ) ≥ 2) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - 8 := by
  have s1 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*alpha <= 2
      have s6 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
        try push_cast at hw
        linarith [hw]
      have s7 : (G.diam : ℤ) ≥ 2 := by linarith [hn2]
      have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s9]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s6, s7, s8, s9, s11]
      have s13 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s12; omega
      have s14 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s15 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s16 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s6, s7, s14, s15]
      have s17 : (G.indepNum : ℤ) ≥ 2 := by have hr := s16; omega
      have s18 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s19 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s20 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s18, s19]
      have s21 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 8 := by linarith [s13, s17, s20]
      linarith [s21]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]

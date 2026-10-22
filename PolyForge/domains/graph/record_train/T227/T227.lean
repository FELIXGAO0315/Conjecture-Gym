import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T227 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ (G.cliqueNum : ℤ)) :
    2 * (G.maxDegree : ℤ) ≥ 2 * (Fintype.card V : ℤ) - 5 * (G.indepNum : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s6])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s9 : 2 * (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4, s7, s8]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s9, heq_gallai, heq_tree]

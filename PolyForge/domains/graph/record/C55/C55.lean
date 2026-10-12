import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C55 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) :
    (G.radius.toNat : ℤ) ≥ -(G.indepNum : ℤ) + (G.diam : ℤ) + 1 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
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
  have s5 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s5]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : 2 * (G.indepNum : ℤ) - 2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3, s4, s6]
  have s8 : (G.indepNum : ℤ) - (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ 1 := by have hr := s7; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s8, heq_gallai, heq_tree]

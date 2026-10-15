import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C38 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) ≤ 3) :
    (G.maxDegree : ℤ) ≥ 3 * (G.diam : ℤ) - 13 := by
  have s1 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
    have hw := diam_le_card_sub_one_int G (isTree_connected G hp1)
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hw := handshake_max_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.indepNum : ℤ) ≥ -3 := by linarith [hn1]
  have s6 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s6]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s8 : -(G.diam : ℤ) ≥ -5 := by linarith [s3, s1, s4, s5, s7]
  have s9 : (G.maxDegree : ℤ) ≥ 0 := by positivity
  have s10 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [s3, s4, s5, s7]
  have s11 : 6 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ (6 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s10]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s12 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s13 : 3 * (G.maxDegree : ℤ) - 9 * (G.diam : ℤ) ≥ -40 := by linarith [s1, s2, s8, s11, s12]
  have s14 : (G.maxDegree : ℤ) - 3 * (G.diam : ℤ) ≥ -13 := by have hr := s13; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s14, heq_gallai, heq_tree]

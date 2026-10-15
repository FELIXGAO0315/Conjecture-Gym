import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C183 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2) :
    (G.minDegree : ℤ) ≤ 3 * (G.indepNum : ℤ) - 5 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s7 : (G.indepNum : ℤ) ≥ 2 := by linarith [s1, s2, s3, s5, s6]
  have s8 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s9 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s10 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s1, s2, s3, s5, s6]
  have s11 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s10]) (by linarith [s9])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s12 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s13 : -2 * (G.minDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 9 := by linarith [s7, s1, s8, s3, s5, s11, s12]
  have s14 : -(G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 5 := by have hr := s13; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s14, heq_gallai, heq_tree]

import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C243 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 3) :
    (G.indepNum : ℤ) ≥ (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) + 4 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hw := handshake_min_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s5 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [hn1]
  have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s8 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 5 := by linarith [s6, s2, s5, s7]
  have s9 : (G.indepNum : ℤ) ≥ 3 := by linarith [s4, s6, s2, s5, s7]
  have s10 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s9]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : (G.minDegree : ℤ) ≥ 0 := by positivity
  have s12 : (Fintype.card V : ℤ) ≥ 6 := by linarith [s4, s6, s2, s5, s7]
  have s13 : -6 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 6) * ((G.minDegree : ℤ) - 0) :=
      mul_nonneg (by linarith [s12]) (by linarith [s11])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s14 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s15 : -3 * (G.minDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 10 := by linarith [s1, s2, s5, s8, s10, s13, s14]
  have s16 : -(G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 4 := by have hr := s15; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s16, heq_gallai, heq_tree]

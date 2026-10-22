import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C209 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.indepNum : ℤ) ≥ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.indepNum : ℤ) ≥ 3 * (G.cliqueNum : ℤ) - 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_card_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.indepNum : ℤ) - 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 3 * (Fintype.card V : ℤ) - 9 * (G.cliqueNum : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ -14 := by linarith [s1, s2, s3, s4, s5]
  have s7 : (Fintype.card V : ℤ) - 3 * (G.cliqueNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ -4 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s7, heq_gallai, heq_tree]

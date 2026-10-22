import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T409 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) + 2 * (G.indepNum : ℤ) - 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
    have hw := tau_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) ≥ 3 := by
    have hw := three_le_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : 2 * (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) + 4 * (G.indepNum : ℤ) ≥ 9 := by linarith [s1, s2, s3, s4, s5]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) ≥ 5 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]

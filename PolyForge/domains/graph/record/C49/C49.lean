import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C49 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ (G.indepNum : ℤ)) :
    (G.vertexCoverNum.toNat : ℤ) ≥ 2 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4]
  have s6 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 2 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]

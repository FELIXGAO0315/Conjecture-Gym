import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C83 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) :
    (G.cliqueNum : ℤ) ≥ 2 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : 2 * (G.cliqueNum : ℤ) ≥ 3 := by linarith [s1, s2]
  have s4 : (G.cliqueNum : ℤ) ≥ 2 := by have hr := s3; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s4, heq_gallai]

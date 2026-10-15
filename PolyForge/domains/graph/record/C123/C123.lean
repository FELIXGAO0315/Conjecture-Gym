import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C123 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.indepNum : ℤ) ≥ -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) + 2 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 2 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]

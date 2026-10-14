import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C261 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.maxDegree : ℤ) + 2 * (G.cliqueNum : ℤ) + 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 6 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 4 * (G.cliqueNum : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : 3 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 1 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]

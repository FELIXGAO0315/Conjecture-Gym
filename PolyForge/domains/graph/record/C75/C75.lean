import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C75 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≥ 6) :
    (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) - 2 := by
  have s1 : (Fintype.card V : ℤ) ≥ 6 := by linarith [hn2]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s3 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -2 * (G.maxDegree : ℤ) + 4 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : -(G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s4; omega
  linarith [s5]

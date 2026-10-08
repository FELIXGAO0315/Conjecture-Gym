import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C108 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0) (hn2 : (Fintype.card V : ℤ) ≥ 5) :
    (G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) ≥ 3 := by
  have s1 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
    have hw := min_le_max_int G
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn2]
  have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s4 : 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : 2 * (G.maxDegree : ℤ) ≥ 1 := by linarith [s1, s3, s4]
  have s6 : (G.maxDegree : ℤ) ≥ 1 := by have hr := s5; omega
  have s7 : 2 * (G.minDegree : ℤ) ≥ 1 := by linarith [s3, s4]
  have s8 : (G.minDegree : ℤ) ≥ 1 := by have hr := s7; omega
  have s9 : (G.maxDegree : ℤ) + 2 * (G.minDegree : ℤ) ≥ 3 := by linarith [s6, s8]
  linarith [s9]

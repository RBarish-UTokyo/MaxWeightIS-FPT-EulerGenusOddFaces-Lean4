module

public import MWIS.Recovery
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Positivity

/-!
# Exact integer optimization by bounded threshold search

The executable high-bit search makes exactly one threshold query per output
bit. Its transcript records the actual queried thresholds. A correct threshold
predicate yields the exact optimum and the binary perturbation decoder recovers
the unique maximizing vertex set.

Prepared 2026-10-23.
-/

@[expose] public section
namespace MWIS.AlgorithmThresholdSearch

/-- Search output with the actual finite query transcript. -/
structure Result where
  value : ℕ
  queries : List ℕ
  deriving Repr

/-- Try the remaining output bits in descending order. -/
def run (test : ℕ → Bool) : ℕ → ℕ → Result
  | 0, lower => ⟨lower, []⟩
  | bits + 1, lower =>
      let query := lower + 2 ^ bits
      let next := run test bits (if test query then query else lower)
      ⟨next.value, query :: next.queries⟩

/-- Optimize over integers below `2 ^ bits`. -/
def solve (test : ℕ → Bool) (bits : ℕ) : ℕ := (run test bits 0).value

/-- The transcript has exactly one query for each requested bit. -/
theorem queries_length (test : ℕ → Bool) (bits lower : ℕ) :
    (run test bits lower).queries.length = bits := by
  induction bits generalizing lower with
  | zero => rfl
  | succ bits ih => simp only [run, List.length_cons, ih]

/-- The interval invariant recovers the unique feasible threshold boundary. -/
theorem run_correct (test : ℕ → Bool) (opt bits lower : ℕ)
    (htest : ∀ t, test t = true ↔ t ≤ opt)
    (hlo : lower ≤ opt) (hhi : opt < lower + 2 ^ bits) :
    (run test bits lower).value = opt := by
  induction bits generalizing lower with
  | zero =>
    simp only [pow_zero] at hhi
    change lower = opt
    omega
  | succ bits ih =>
    have hp : 2 ^ (bits + 1) = 2 ^ bits + 2 ^ bits := by rw [pow_succ]; omega
    rw [hp] at hhi
    by_cases h : test (lower + 2 ^ bits) = true
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false]
      exact ih _ ((htest _).mp h) (by omega)
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false]
      have hn : ¬lower + 2 ^ bits ≤ opt := fun ht => h ((htest _).mpr ht)
      exact ih _ hlo (by omega)

/-- Correctness needs threshold answers only in the searched interval. -/
theorem run_correct_bounded (test : ℕ → Bool) (opt bits lower : ℕ)
    (htest : ∀ t, lower ≤ t → t < lower + 2 ^ bits → (test t = true ↔ t ≤ opt))
    (hlo : lower ≤ opt) (hhi : opt < lower + 2 ^ bits) :
    (run test bits lower).value = opt := by
  induction bits generalizing lower with
  | zero =>
    simp only [pow_zero] at hhi
    change lower = opt
    omega
  | succ bits ih =>
    have hpos : 0 < 2 ^ bits := by positivity
    have hp : 2 ^ (bits + 1) = 2 ^ bits + 2 ^ bits := by rw [pow_succ]; omega
    rw [hp] at hhi htest
    have hquery := htest (lower + 2 ^ bits) (by omega) (by omega)
    by_cases h : test (lower + 2 ^ bits) = true
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false]
      apply ih _ (fun t ht ht' => htest t (by omega) (by omega)) (hquery.mp h)
      omega
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false]
      apply ih _ (fun t ht ht' => htest t ht (by omega)) hlo
      have hn : ¬lower + 2 ^ bits ≤ opt := fun ht => h (hquery.mpr ht)
      omega

/-- Every actual query lies in the original search interval. -/
theorem queries_range (test : ℕ → Bool) (bits lower q : ℕ)
    (hq : q ∈ (run test bits lower).queries) : lower ≤ q ∧ q < lower + 2 ^ bits := by
  induction bits generalizing lower with
  | zero => simp [run] at hq
  | succ bits ih =>
    have hpos : 0 < 2 ^ bits := by positivity
    have hp : 2 ^ (bits + 1) = 2 ^ bits + 2 ^ bits := by rw [pow_succ]; omega
    by_cases h : test (lower + 2 ^ bits) = true
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false, List.mem_cons] at hq
      rcases hq with rfl | hq
      · omega
      · have hi := ih _ hq
        omega
    · simp only [run, h, Bool.false_eq_true, ↓reduceIte, ite_false, List.mem_cons] at hq
      rcases hq with rfl | hq
      · omega
      · have hi := ih _ hq
        omega

/-- Exact bounded integer optimization. -/
theorem solve_correct (test : ℕ → Bool) (bits opt : ℕ)
    (hopt : opt < 2 ^ bits)
    (htest : ∀ t < 2 ^ bits, test t = true ↔ t ≤ opt) :
    solve test bits = opt :=
  run_correct_bounded test opt bits 0 (fun t _ ht => htest t (by simpa using ht))
    (Nat.zero_le _) (by simpa using hopt)

/-- All query arguments fit in the output bit width. -/
theorem query_size (test : ℕ → Bool) (bits q : ℕ)
    (hq : q ∈ (run test bits 0).queries) : q.size ≤ bits := by
  exact Nat.size_le.mpr (by simpa using (queries_range test bits 0 q hq).2)

/-- A uniform per-query work bound is multiplied by exactly the output width. -/
theorem query_work_bound (test : ℕ → Bool) (bits : ℕ) (work : ℕ → ℕ) (bound : ℕ)
    (hwork : ∀ q < 2 ^ bits, work q ≤ bound) :
    ((run test bits 0).queries.map work).sum ≤ bits * bound := by
  have h : ∀ q ∈ (run test bits 0).queries, work q ≤ bound := by
    intro q hq
    exact hwork q (by simpa using (queries_range test bits 0 q hq).2)
  have hs : ∀ qs : List ℕ, (∀ q ∈ qs, work q ≤ bound) →
      (qs.map work).sum ≤ qs.length * bound := by
    intro qs
    induction qs with
    | nil => simp
    | cons a qs ih =>
      intro ha
      have h1 := ha a (by simp)
      have h2 := ih (fun q hq => ha q (by simp [hq]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
      omega
  simpa only [queries_length] using hs _ h

/-- Exact value optimization followed by the proved incidence-mask decoder. -/
theorem recover_encoded_optimum (test : ℕ → Bool) (bits n : ℕ) (w : ℕ → ℤ)
    (feasible : Finset ℕ → Prop) (hbound : ∀ I, feasible I → I ⊆ Finset.range n)
    (I : Finset ℕ) (hI : feasible I)
    (hmax : ∀ J, feasible J → Recovery.encodedValue n w J ≤ Recovery.encodedValue n w I)
    (hnonneg : 0 ≤ Recovery.encodedValue n w I)
    (hsize : (Recovery.encodedValue n w I).toNat < 2 ^ bits)
    (htest : ∀ t < 2 ^ bits, test t = true ↔ (t : ℤ) ≤ Recovery.encodedValue n w I) :
    feasible (Recovery.decode (solve test bits) n) ∧
      (∀ J, feasible J → Recovery.weight w J ≤
        Recovery.weight w (Recovery.decode (solve test bits) n)) := by
  have hs := solve_correct test bits (Recovery.encodedValue n w I).toNat hsize
    (fun t ht => (htest t ht).trans (by omega))
  have hs' : (solve test bits : ℤ) = Recovery.encodedValue n w I := by omega
  rw [hs']
  obtain ⟨hm, hd, _⟩ := Recovery.recovery_of_encoded_optimum n w feasible hbound I hI hmax
  rw [hd]
  exact ⟨hI, hm⟩

end MWIS.AlgorithmThresholdSearch
end

import ConceptualMathematics.Sorried.Article1

namespace CM

/-!
Equality of maps of sets (p. 23)
-/
example {A B : Type} {f g : A → B}
    : (∀ a : Point A, f ∘ a = g ∘ a) → f = g := by
  intro h
  ext a'
  exact congrFun (h (fun _ ↦ a')) ()

end CM

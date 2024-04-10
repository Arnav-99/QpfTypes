import Qpf
open MvQPF

#check Vec.nil

/-!
  Let us start with a simple example of an inductive type: lists
  ```lean4
  inductive QpfList (α : Type u)
   | nil : QpfList α
   | cons : α →  QpfList α → QpfList α
  ```

  Since each argument to each constructor is purely a variable, or purely the resulting type `QpfList α`,
  we can translate this type to a fixpoint of some polynomial functor, which we'll call `QpfList.Shape`.

  Since we'll be taking a fixpoint, `QpfList.Shape` is indeed a binary functor, where the first argument
  will be passed on as `α`, and the second argument will be representing `QpfList α`.
  We can think of it like the following (non-recursive!) inductive type
  ```lean4
  inductive QpfList.Shape' (α β : Type u)
    | nil  : Shape' α β
    | cons : α → β → Shape' α β
  ```

  Of course, we won't actually define the type as such, instead, recall that polynomial functors are
  encoded by a "head" type, which may not depend on `α`, and a "child" type, that does depend on `α`.

-/
namespace QpfList
  /-
    The aforementioned "head" type is a simple enumeration of all constructors
  -/
  inductive HeadT
    | nil
    | cons

  /-
    The "child" type tells us for each constructor (i.e., element of `HeadT`) and each type argument,
    how many instances of that type we need, through the cardinality of `ChildT a i`.

    In this case, the `nil` constructor takes no argument, while `cons` takes one instance of both
    arguments, hence we use the empty and unit types, respectively.
  -/
  abbrev ChildT : HeadT → TypeVec 2
    | HeadT.nil , _ => Empty
    | HeadT.cons, _ => Unit

  /-
    We define the polynomial functor
  -/
  abbrev P := MvPFunctor.mk HeadT ChildT

  /- The `MvFunctor` instance is defined on `P` action on objects-/
  abbrev F := P.Obj

  /-
    Of course, each polynomial functor is a (multivariate) quotient of a polynomial functor, and
    this is automatically inferred
  -/
  example : MvQPF F := inferInstance

  /- We define `QpfList'` as the fixpoint of `P` in the last argument -/
  abbrev QpfList' : TypeFun 1 := Fix QpfList.F

  /- And define a curried version for final use -/
  abbrev QpfList := QpfList'.curried

  example : MvQPF QpfList' := inferInstance

/-
  # Constructors
  We manually define the constructors in terms of `Fix.mk`
-/

  @[reducible]
  def nil {α : Type} : QpfList α :=
    Fix.mk ⟨HeadT.nil, fun _ emp => by contradiction⟩

  -- CC: Why does marking this as @[reducible] case errors later?
  -- Particularly with `funext`, `congr`, etc.
  def cons {α} (hd : α) (tl : QpfList α) : QpfList α :=
    Fix.mk ⟨HeadT.cons, fun i _ => match i with
                          | 0 => tl
                          | 1 => hd
    ⟩


  -- Curiously, similar "constructors" can be made for the uncurried version QpfList'
  def nil' {α : Type} : QpfList' α :=
    Fix.mk ⟨HeadT.nil, fun _ emp => by contradiction⟩

  def cons' {α : Type} (hd : α) (tl : QpfList' α): QpfList' α :=
    Fix.mk ⟨HeadT.cons, fun i _ => match i with
                          | 0 => tl
                          | 1 => hd
    ⟩

  -- The list `[1, 2, 3]`
  example : QpfList Nat :=
    cons 1 $ cons 2 $ cons 3 $ nil

  example : QpfList' Nat :=
    cons' 1 $ cons' 2 $ cons' 3 $ nil'

  /-
    Pattern matching does not work like one would expect, but we'll ignore it for now

  def mul2 : QpfList Nat → QpfList Nat
    | nil        => nil
    | cons hd tl => cons (2*hd) (mul2 tl)
  -/

  def rec {α} {motive : QpfList α → Sort _} :
      (motive nil) → ((hd : α) → (tl : QpfList α) → motive tl → motive (cons hd tl))
      → (t : QpfList α) → motive t := by
    intro h_nil h_rec
    apply Fix.ind
    rintro ⟨a, f⟩ h_rec_motive
    cases a
    · convert h_nil
    · /- `h_rec_motive` is a lifted predicate over the multi-variate functor
         that gives back the motive on list under `f`. However, to access the
         motive on our particular `f`, we go through `MvQPF.liftP_iff`, which
         gives us access to the abstracted (i.e., quotiented) version of our
         data type. However, since `QpfLists` aren't behaviorally quotients
         (meaning that order is preserved), the lifting operation that gives
         us the motive on the abstracted version also holds on the concrete
         version, since they're the same thing. -/
      rw [MvQPF.liftP_iff] at h_rec_motive
      rcases h_rec_motive with ⟨a, _, h_abs, d⟩
      /- Interestingly, typing `injection h_abs` causes one of the generated
         hypotheses to be `Heq f b` instead of `f = b`, likely because `a` is
         involved in other terms, and so Lean doesn't want to commit to an
         equality just yet.
         So we do the slightly more roundabout thing and case on `a`. -/
      cases a <;> injection h_abs <;> try contradiction
      rename _ => h; subst h
      /- Alternatively, we can do `simp [cons] at h_rec`
          to avoid unfolding `cons` in the generated goal after `convert`.
          However, I think it's cleaner this way, since it follows the
          analogous form of induction with lists. -/
      convert h_rec (f (.fs .fz) ()) (f .fz ()) (d .fz ())
      -- The types don't exactly match, since `cons` hides some machinery.
      -- `convert` generates a new goal for us.
      rw [cons]
      congr
      ext
      /- It turns out that Lean is very smart with "simple" types. Here, we
         want to show that `f` and an anonymous function are equal under two
         arguments. But because we can peek under the anonymous function,
         we can let Lean split on the branches with `split`. Thus, we find
         that the two are equal, and can close each branch with `rfl`. -/
      split <;> rfl
      done
    done

#check PSum
#check PSigma
#check PProd

#check List.rec
#check TypeVec.id
#check MvFunctor.map
#check TypeVec.comp
#check PFin2

  /- CC: Because QpfLists are W-types, meaning actual concrete QpfLists are
         types, and not instances of a type, to say that a list `l` is either
         `nil` or `cons` is actually a statement on types.
         The correct way of phrasing it is using `PSigma` and `PSum`. -/
  #check PSigma
  theorem cases_eq : ∀ (l : QpfList α), l = nil ⊕' Σ' hd tl, l = cons hd tl := by
    --intro l
    apply Fix.drec
    rintro ⟨a, f⟩
    cases a
    · left; simp [nil]
      congr
      simp [MvFunctor.map, MvPFunctor.map, P]
      congr
      ext
      contradiction
    · right
      refine' ⟨(f (.fs .fz) ()), ?_⟩
      -- makes lhs look a bit more like nil case
      simp [MvFunctor.map, MvPFunctor.map]
      simp [cons]
      -- tl mysteriously disappears after next step
      apply PSigma.mk
      congr
      unfold TypeVec.comp
      ext fnIndex unit
      rw [← (@PFin2.ofFin2_toFin2_iso 2 fnIndex)]
      cases PFin2.ofFin2 fnIndex
      simp [PFin2.toFin2]



      -- CC: Unclear why this isn't typing correctly, but it does above
      stop
      refine' ⟨(f .fz ()), ?_⟩
      done

end QpfList

-- questions:
-- PSigma.mk
-- convert tactic usage
--

export QpfList (QpfList QpfList')

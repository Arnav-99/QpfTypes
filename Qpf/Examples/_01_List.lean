import Qpf
open MvQPF

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

  def nil {α : Type} : QpfList α :=
    Fix.mk ⟨HeadT.nil, fun _ emp => by contradiction⟩


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

  theorem cases_eq : ∀ (l : QpfList α), l = nil ⊕' Σ' hd tl, l = cons hd tl := by
    intro l
    have : ∃ l', Fix.mk l' = l := by
      use Fix.dest l; exact Fix.mk_dest l
    sorry
    -- It is likely that `cases_eq` is helpful for proving `rec`, but since it
    -- doesn't talk about `motive`, it might not actually be that helpful.
    -- Besides, it might also be of similar difficult to prove it wrt rec!
    done

#check List.rec
#check Fix.ind
#check Fix.mk_dest
#check PFin2.fz

#check MvFunctor.map

  def rec {α} {motive : QpfList α → Sort _} :
    (motive nil) → ((hd : α) → (tl : QpfList α) → motive tl → motive (cons hd tl))
    → (t : QpfList α) → motive t := by

  intro h_nil h_rec
  apply Fix.ind
  intro x hx
  rcases x with ⟨a, f⟩
  cases a
  · rw [nil] at h_nil
    convert h_nil
  · have tl := f .fz ()
    have hd := f (.fs .fz) ()
    simp [Vec.reverse, TypeVec.append1] at hd tl
    simp [Vec.reverse, Matrix.vecCons, Fin.rev, Fin.cons, Fin.cases] at hx
    have := h_rec hd (cast (by
      unfold QpfList TypeFun.curried
      simp [TypeFun.curriedAux, TypeFun.reverseArgs]) tl)
      (cast (by sorry) hx)
    rcases hx with ⟨y, hy⟩


    convert this
    unfold cons
    apply congrArg
    simp
    apply funext
    intro x
    rw [← (@PFin2.ofFin2_toFin2_iso 2 x)]

    cases (PFin2.ofFin2 x) with
    | fz => {
      apply funext
      intro x
      simp [MvPFunctor.B, PFin2.toFin2, ChildT] at x
      simp [PFin2.toFin2]
      have something : x = () := by trivial
      rw [something]
      -- can't recognize previous binding of f 0 () to hd
      -- adding sorry errors
      sorry
    }

    | fs n => {
      cases n with
      | fs n' => contradiction
      | fz => {
        apply funext
        intro x
        simp [MvPFunctor.B, PFin2.toFin2, ChildT] at x
        simp [PFin2.toFin2]
        have something : x = () := by trivial
        rw [something]
        -- error when forcing x to ()
        -- can't recognize previous binding of f 1 () to tl
        -- adding sorry causes universe error
        sorry
      }
    }

    -- Something like the following might be possible
    -- convert h_rec hd y hy
    done
  done
  --apply Fix.drec (β := motive)

  --rcases Fix.dest l with ⟨a, f⟩
  /-
  have := Fix.mk_dest l

  rw [← Fix.mk_dest l]
  match h_dest : Fix.dest l with
  | ⟨a, f⟩ =>
    cases a
    · rw [h_dest] at this
      rw [nil] at h_nil
      convert h_nil
      --exact h_nil
    · simp [TypeVec.Arrow, ChildT] at f
      have tl := f .fz ()
      have hd := f (.fs .fz) ()
      simp [Vec.reverse, Vec.append1, TypeVec.append1] at hd tl
      convert h_rec hd (cast ?C tl)
      · congr

        --exact cast l

        done
      · unfold QpfList TypeFun.curried
        simp [TypeFun.curriedAux, TypeFun.reverseArgs]
        done

      done
      --suffices
      --apply h_nil

      done
    done
    -/
  --rcases Fix.dest l with ⟨a, f⟩

  -- Below doesn't work for some reason...
  --rcases cases_eq l with (h | h)
  --done
  /-
  apply Or.elim (cases_eq l)
  · rintro rfl; exact h_nil
  · rintro ⟨hd, tl, rfl⟩
    exact h_rec hd tl -/

  /-fun base_case rec_case t => by
    let t' := Fix.dest t;
    simp [MvPFunctor.Obj] at t'
    rcases t' with ⟨a, f⟩
    cases a <;> simp [MvPFunctor.B] at f

    let g := fun ⟨a, f⟩ => match a with
      | HeadT.nil  => cast (
                        by  delta nil;
                            apply congrArg; apply congrArg;
                            simp [MvFunctor.map];
                            conv in (fun x emp => _) => {
                              tactic => funext x y; contradiction;
                            }
                      ) base_case
      | HeadT.cons => by simp [MvPFunctor.B, HeadT, ChildT] at f
                         skip
                         sorry
                      cast (
                        _
                      ) (rec_case (f (Fin2.fz) (by simp [P.B])) _)
    Fix.drec (β := motive) g t -/


end QpfList

export QpfList (QpfList QpfList')

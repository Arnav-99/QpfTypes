import Qpf
import Qpf.Examples._01_List
import Qpf.Macro.Tactic.FinDestr
import Qpf.MathlibPort.Fin2

open MvQPF

-- open List

-- inductive RoseTree (β : Type) : Type _
--   | node : β → List (RoseTree β) → RoseTree β

-- #check RoseTree.rec

inductive Hello (α : Type _)
  | fst : α → α → Hello α
  | snd : α → Hello α
  | thd : Hello α

inductive RT (α : Type _) : Type _
  | node : α → List (RT α) → RT α

#check RT.rec

--theorem tryItOut : ∀ (t : RT α),

#check Hello.rec

namespace QpfTree
  namespace Shape
    /-
      Since there is only one constructor, `def HeadT := Unit` would also have sufficed
    -/
    inductive HeadT
      | node

    abbrev ChildT : HeadT → TypeVec 2
      | .node => ![PFin2 1, PFin2 1]

    abbrev P := MvPFunctor.mk HeadT ChildT

    abbrev F := TypeFun.curried P.Obj

    instance : MvFunctor P.Obj := by infer_instance
  end Shape

  /-
    Before we can take the fixpoint, we need to compose this shape functor with QpfList in the second
    argument. Effectively, we want to define
    ```
      F α β := Shape.F α (QpfList β)
    ```

    Note that we don't care too much about whether `F` is a polynomial functor, we just require it
    to be a QPF, so we'll invoke the composition of QPFs here.

    To do so, we have to supply two binary functors to be composed with `Shape.P.Obj`.
    The first functor is trivial, it's the projection to the second argument (we count the
    arguments right-to-left, since that is how the `Vec`s are built).
    ```
      G₁ α β := α           -- (hence, G₁ := Prj 1)
    ```
    The second functor is a bit more involved. We want to invoke `QpfList`, which expects a single
    argument, but `G₂` should be a binary functor. Additionally, the argument we want to apply
    `QpfList` to is `β`, the second argument, so we compose `QpfList` with a projection functor
    ```
      G₂ α β := QpfList β   -- (hence, G₂ := Comp QpfList' ![Prj 0])
    ```
  -/

  #check Fin2
  #check Fix.mk
  #check TypeFun

  abbrev G' (j : Fin2 1) : TypeVec 2 → Type := Prj 0

  abbrev G (i : Fin2 2) : TypeVec 2 → Type :=
    match i with
    | 0 => Comp QpfList' G'
    | 1 => Prj 1

  #check ![@Prj 2 0]
  #check !![@Prj 2 0]

  abbrev Base : TypeFun 2
    := Comp Shape.P.Obj G

  def F' := Shape.P.Obj

  instance : MvFunctor Shape.P.Obj := by infer_instance
  instance : MvQPF Shape.P.Obj := by infer_instance

  instance (i : Fin2 2) : MvFunctor (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      simp [G]
      split
      · contradiction      -- Alternatively, rename _ => h; revert h; exact Fin2.elim0
      · infer_instance

  instance : MvFunctor Base := by infer_instance

  -- CC: This is having trouble type-checking?
  --instance : MvQPF (fun (i : Fin2 1) =>
  --    Matrix.vecCons (Prj 1) ![] (Fin.rev (PFin2.toFin (PFin2.ofFin2 i)))) := by

  --  done\

  #check Comp

  instance (i : Fin2 2) : MvQPF (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      simp [G]
      match s with
      | .fz =>
        simp
        infer_instance
        done
      | .fs s' => revert s'; exact Fin2.elim0

  instance : MvQPF Base := by infer_instance

  abbrev QpfTree' := Fix Base
  abbrev QpfTree  := TypeFun.curried QpfTree'

  #check @Prj 2 1
  #check Shape.F
  #check Shape.P.Obj
  #check Vec.append1

  #check ![@Prj 2 0]
  #check !![@Prj 2 0]
  #check TypeFun.curried

  instance : MvFunctor QpfList' := by infer_instance

  -- node constructor

  def node (a : α) (children : QpfList (QpfTree α)) : QpfTree α :=
    Fix.mk ⟨Shape.HeadT.node,
            fun i _ => match i with
            | 0 =>  by
              convert children
              simp
              unfold G
              simp [Comp, G', Prj]
              congr
              simp
              apply funext
              simp
              simp [QpfTree, QpfTree', TypeVec.append1]
              congr
              simp
            | .fs .fz => a
    ⟩

  -- rec for rose trees

  #check Subtype
  #check Prod

  def helper (a : Int) : Int := a
  def int' := { z : Int // z % 2 = 0 }

/-
  def rec {α} {motive : QpfTree α → Sort _}
    {motive₂ : ∀ (a : α) (l : QpfList ({ T : QpfTree α // motive T})),
      motive (node a (l.map ..))}

    {motive₃ : ∀ (a : α) (l : QpfList (QpfTree α)),
      ∃ l' : QpfList ({ T : QpfTree α // motive T}), motive (node a (l'.map ..))}
  := by
  sorry

  RT.rec.{u, u_1} {α : Type u_1} {motive_1 : RT α → Sort u} {motive_2 : List (RT α) → Sort u}
  (node : (a : α) → (a_1 : List (RT α)) → motive_2 a_1 → motive_1 (RT.node a a_1)) (nil : motive_2 [])
  (cons : (head : RT α) → (tail : List (RT α)) → motive_1 head → motive_2 tail → motive_2 (head :: tail)) (t : RT α) :
  motive_1 t
  done -/

  def rec {α} {motive_1 : QpfTree α → Sort _} {motive_2 : QpfList (QpfTree α) → Sort _} :
  ((root : α) → (children : QpfList (QpfTree α)) → (motive_2 children) → (motive_1 (node root children)))
  → (motive_2 (QpfList.nil))
  → ((head : QpfTree α) → (tail : QpfList (QpfTree α)) → motive_1 head → motive_2 tail → motive_2 (QpfList.cons head tail))
  → (t : QpfTree α) → (motive_1 t) := by
    intro h_rec h₁ h₂
    apply Fix.ind
    rintro ⟨a, f⟩ h_rec_motive
    cases a
    rw [MvQPF.liftP_iff] at h_rec_motive
    rcases h_rec_motive with ⟨a, _, h_abs, d⟩
    cases a
    -- CC: Why doesn't (f .fz .fz) work here? Unfold defs/abbrevs?
    convert h_rec (f (.fs .fz) .fz) ?_ ?_ --(d .fz ?_)
    apply QpfList.rec h₁ h₂ _
    --rename (P ↑Shape.P).A => a
    injection h_abs
    rename Shape.HeadT.node = _ => h_node
    simp [Shape.HeadT.node] at h_node
    subst h_node
    rename f = _ => h_f
    subst h_f
    simp
    convert h_rec ?_ ?_ ?_
    have child_list : QpfList (QpfTree α) := by
      convert (f .fz .fz)
      simp
      unfold G
      simp
      simp [Comp, G', Prj]
      simp [QpfList, QpfTree, QpfTree', TypeFun.curried, TypeFun.curriedAux]
      congr

    have child_list_motive : motive_2 child_list := by
      apply QpfList.rec
      -- do I need additional arguments in recursion principle?
      sorry
      sorry

    convert h_rec (f (.fs .fz) .fz) child_list child_list_motive
    unfold node
    congr
    ext a1 a2
    split
    sorry
    congr
    sorry

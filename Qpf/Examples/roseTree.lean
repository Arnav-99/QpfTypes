import Qpf
import Qpf.Examples._01_List
import Qpf.Macro.Tactic.FinDestr
import Qpf.MathlibPort.Fin2

namespace Testing

inductive NonRec (α : Type _)
  | fst : α → α → NonRec α
  | snd : α → NonRec α
  | thd : NonRec α

/- CC: Notice how a separate hypothesis is made for each constructor, and each
       constructor's arguments appear in the hypothesis, but because there are
       no appearances of a `NonRec` type in any constructor, all that's needed
       is a proof that the motive holds on the constructed `NonRec` object
       with those constructor arguments.  -/
#check NonRec.rec
#check true

-- "all that's needed
--        is a proof that the motive holds on the constructed `NonRec` object
--        with those constructor arguments."

inductive Rec₁ (α : Type _) : Type _
  | node : α → Rec₁ α → Rec₁ α → Rec₁ α

/- CC: Here, we have something that looks like a binary tree, with two apperances
       of the inductive type in the constructor. As a result, the motive must
       hold for each of the two recursive arguments, before we prove that
       the motive holds on the constructed `Rec₁` object. -/
#check Rec₁.rec

inductive Rec₂ (α : Type _) : Type _
  | node : α → Rec₂ α → List (Rec₂ α) → Rec₂ α

/- CC: Finally, we see a type that has an appearance of the type itself in an
       argument, but folded into a different inductive type. Typically, we
       just give the constructor's recursive arugments to the same motive to
       start, but because the motive only takes a `Rec₂`, we require a new
       motive that works on `List (Rec₂ α)`. Hence the two motives created
       for the recursor. In a sense, the motive is required for us to talk
       about the `Rec₂ α` objects "hiding" in the list. Otherwise, we don't
       have access to the `Rec₂` objects in the list. The user-supplied motives
       of the right types ensure that we can properly recurse (along with the
       constraint that the List motive does, in fact, "implement" induction.) -/
#check Rec₂.rec

-- AS: AH, so the argument type pertinent to motive_2 ensures that the
-- motive on lists implements induction on lists

end Testing


open MvQPF

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

    -- abbrev F := TypeFun.curried P.Obj
    -- AS: trying to mirror QpfList case by removal of TypeFun.curried
    abbrev F := P.Obj

    instance : MvFunctor P.Obj := by infer_instance

    instance : MvQPF F := by infer_instance

    -- AS: the first difference seen between the 2 proofs was the non-recognition
    -- of the multivariate functor as a QPF in the rose tree case, so that has
    -- been experimentally added here
    instance : MvQPF P := by infer_instance

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

  -- CC: There's probably a more compact way of writing this using `TypeVec.Arrow` or `Prj.map`

  #check TypeVec.Arrow
  #check Prj.map
  #print Prj

  abbrev G (i : Fin2 2) : TypeVec 2 → Type :=
    match i with
    | 0 => Comp QpfList' (fun _ => Prj 0)
    | 1 => Prj 1

  -- AS: alternative, compact definition of G


  abbrev Base : TypeVec 2 → Type
    := Comp Shape.P.Obj G

  instance : MvFunctor Shape.F := by infer_instance
  instance : MvQPF Shape.F := by infer_instance

  instance (i : Fin2 2) : MvFunctor (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      simp [G]
      split
      · contradiction
      · infer_instance

  instance : MvFunctor Base := by infer_instance

  instance (i : Fin2 2) : MvQPF (G i) := by
    match i with
    | .fz => simp [G]; infer_instance
    | .fs s =>
      match s with
      | .fz => simp [G]; infer_instance
      | .fs s' => contradiction

  instance : MvQPF Base := by infer_instance

  abbrev QpfTree' := Fix Base
  abbrev QpfTree  := TypeFun.curried QpfTree'

  instance : MvFunctor QpfList' := by infer_instance

  -- AS: added to match QpfList case
  instance : MvQPF QpfTree' := by infer_instance

  -- node constructor

  def node (a : α) (children : QpfList (QpfTree α)) : QpfTree α :=
    Fix.mk ⟨Shape.HeadT.node,
            fun i _ => match i with
            | 0 =>  by
              convert children
              simp [G, Comp, Prj]
              congr
              apply funext
              simp [QpfTree, QpfTree', TypeVec.append1]
              congr
              simp
            | .fs .fz => a
    ⟩

  -- rec for rose trees

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

  #check TypeVec.comp
  #check MvQPF.abs
  #print MvQPF.abs
  #check MvPFunctor.B

  #check P

  def rec {α} {motive_1 : QpfTree α → Sort _} {motive_2 : QpfList (QpfTree α) → Sort _} :
      ((root : α) → (children : QpfList (QpfTree α))
        → (motive_2 children) → (motive_1 (node root children)))
      → (motive_2 (QpfList.nil))
      → ((head : QpfTree α) → (tail : QpfList (QpfTree α))
        → motive_1 head → motive_2 tail → motive_2 (QpfList.cons head tail))
      → (t : QpfTree α) → (motive_1 t) := by
    intro h_rec h₁ h₂
    apply Fix.ind
    rintro ⟨a, f⟩ h_rec_motive
    cases a
    rw [MvQPF.liftP_iff] at h_rec_motive
    rcases h_rec_motive with ⟨a, b, h_abs, d⟩
    -- difference in behaviour from QpfLists is seen from this point
    -- why is a not an MvQPF here but is one in QpfList?
    -- AS: ensuring that Lean knows P is an MvQPF instance has not changed this
    -- cases' a with headT dependentT
    -- cases headT
    -- simp at dependentT
    -- cases (dependentT (.fz) PFin2.fz)
    injection h_abs
    rename _ => h_f
    -- subst h_f
    have := f .fz
    simp [Shape.ChildT, Shape.HeadT.node] at this
    have := this .fz
    simp [G, QpfList, Base] at this

    convert h_rec (f (.fs .fz) .fz) ?_ ?_
    -- the line above causes the last argument to not have access to the
    -- element of QpfList (QpfTree α), since the latter itself is ?
    simp [node]
    congr
    ext
    --
    -- stop
    split -- CC: dunno why this fails here, but succeeds in list.
    ext
    simp
    split
    ·
      done
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

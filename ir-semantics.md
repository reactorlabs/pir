## The formal language

    x        variables
    L        labels
    Lᶠ       function name labels

    t  ::= ⊤ | ⊥ | int | bool | ...   types
    tₕ ::= (x : t)* ↦ (y : t)*        Partial Heap Type:   TBD!!
    a  ::= x : t                      Formal argument:     name and type

    S  ::= (a*) : t [tₕ]              Function Signature:  formal arguments and heap type
    D  ::= Lᶠ S                       Declaration:         function name and signature

    P ::= (D := F)*                   program:             list of function declarations with signature
    F ::= (S {B})*                    function:            partially typed versions
    B ::= var x* in I                 version body:        variable declarations and code
    I ::= (L ↦ i)*                    instruction stream:  labeled instructions

##### Reserved Names

    main      main function    (execution of program starts here)
    start     start label      (execution of function starts here)

##### Instructions

    i ::=                instructions
    |       x  := e           local variable assignment
    | store(x) := e           store to a global variable
    |       x₁ := load(x₂)    load from a gloabl variable
    | print e
    | x := read               read a literal from the user
    | goto     L
    | branch e L₁ L₂
    | call   x := e (arg*)
    | return e
    | stop

    e ::=     expression
    | se                    simple expression
    | primop(se*)           primitive operation

    se ::=    simple expressions
    | lit                   literals
    | x                     variables
    | `Lᶠ`                  function reference

    lit ::=  literals
    | nil
    | true | false
    | ... | ─1 | 0 | 1 | 2 | ...

    v :=     values
    | lit                   literals
    | Lᶠ                    function reference

##### Signatures

The different signatures of the partially typed versions need to be compatible with the function signature.
For example in

    fun(x₁ : T₁) : T [Tₕ] :=
      (x₁ : T₁') : T' [Tₕ'] {
        ...
      }

we require that.

    T₁ <: T₁'    and    T' <: T     and      Tₕ <: Tₕ'

TBD: define `<:`

#### Example:

    fun(x : ⊤) : ⊤ [⊤ ↦ ⊤] :=
      (x : ⊤) : int [E:⊤ ↦ E] {
        var res;
        call res := toInt(x)
        return (2*res)
      },
      (x : int) : int [E:⊤ ↦ E] {
        return (2*x1)
      }
    main() : ⊤ [⊤ ↦ ⊤] :=
      () : ⊤ [⊤ ↦ ⊤] {
        var res;
        call res := fun(3)
        return res
      }

## Natural operational semantics

    E ::= (x ↦ v)*          lexical environment
    M ::= (x ↦ v)*          global  environment

#### Configuration

    C ::= (P I L K* M E)    configuration
    K ::= (I L x E)         kontinuation
    A ::=                   actions
    | τ
    | store x,v | load x
    | read lit | print lit


### Reduction relation `C ══A══> C'`

The labeled reduction `══A══>` is expressed in terms of an auxiliare relation `─A─>` that allows us to conveniently match the current instruction.
`I` dentotes the current instruction stream and `L` the current label (pc).
Therefore `I(L)` extracts the next instruction to execute.

    [══>]
         P I L K* M E : I(L)  ─A─>  C'
        ───────────────────────────────
         P I L K* M E        ══A══> C'

#### Evaluation of expressions `(C : e)  ──>  v`

We only write the referenced parts of `C` on the lhs.

    [EXPR]
        E : x             ──>    v               if   (x ↦ v) ∈ E
          : lit           ──>    lit
        P : `Lᶠ`          ──>    Lᶠ              if   Lᶠ ∈ dom(P)
        C : primop(se*)   ──>    ⟦primop⟧(v*)    if   C: seᵢ  ──>  vᵢ  ∀i

#### Evaluation of instructions `(C : i) ──A──> C`

We only write the referenced parts of `C` on the lhs and the modified parts of C on the lhs.

##### Memory and IO instructions.

The metafunction `succ` selects the successor label of the immediately following instruction in the instruction stream

    succ (..., L ↦ _, L' ↦ _, ...) L  =  L'

In all of the following instructions `L` is is implicitly updated to `(succ I L)` on the rhs.

     P I L K* M E : i  ╰──A──>  C'
    ────────────────────────────────────────────
     P I L K* M E : i  ───A──>  C'[(succ I L)/L]

Note that there is nothing to prevent a variable name `x` from being used as a local and a global variable at the same time.
If the source language allows shadowing, the compiler frontend is responsible for emitting the right instructions.

Storing something to a local variable is a silent action.
Local variables need to be declared (see the syntax of `F`).

    [LOCAL_ASSIGN]
        E : (x := e)  ╰──τ──>  E[x ↦ v]
            if  e ──> v
            and x ∈ dom(E)

Loads and stores to the global scope.
Variables are declared on first use.

    [GLOBAL_STORE]
        M : (store(x) := e)  ╰─store x,v─>  M[x ↦ v]
            if e ──> v

    [GLOBAL_LOAD]
        M E : (x₁ := load x₂)  ╰─load x₂─>  E[x₁ ↦ v]
            if (x₂ ↦ v) ∈ M

IO operations.
To avoid technical difficulties only literals (e.g. no function references).

    [IO_READ]
        E : (x := read)  ╰─read lit─>  E[x ↦ lit]

    [IO_WRITE]
        (print e)  ╰─print lit─> ()
            if e ──> v

##### Controlflow instruction:

Controlflow is goto based.
To jump or branch we modify the `L` part of the configuration.

    [GOTO]
        goto L          ─τ─>  L

    [BRANCH]
        branch e L₁ L₂  ─τ─>  L₁
            if  e  ──>  true

        branch e L₁ L₂  ─τ─>  L₂
            if  e  ──>  v
            and v  !=  true

Termination is observable.
As a technical device the configuration transitions to all empty sets, to ensure the reduction terminates.

    [STOP]
        stop         ─stop─>  ∅*

##### Call instruction:

The call instructions are a bit more involved.
On a call we create a new local scope which contains all local function arguments and all the declared local variables.
We still need to define `pick-version` which is the metafunction that chooses which version to invoke given the current configuration and the arguments.

    [CALL]
                 e  ──>  Lᶠ                 eₜ ──>  vₜ                (Lᶠ S := F) ∈ P
         E' := {(x ↦ v)*, (y ↦ nil)*}     K := (I L x E)                 where S = ((x : _)*)
        ────────────────────────────────────────────────────────      B :=  pick─version(Lᶠ, C, v*)
         P I L K* E : call x = e (e*)  ─τ─>  I' start (K K*) E'          where B = var y* in I'

    [RETURN]
          e  ──>  v       E' := E[x ↦ v]
        ───────────────────────────────────      K = (I L x E)
        (K K*) : return e  ─τ─>  I L K* E'

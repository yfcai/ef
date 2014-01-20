/** the type system */
trait ExistentialF
    extends CompositionallyTypeableModules
       with IntsAndBools
       with Unification
{
  // MODULE OBLIGATIONS

  // Domain is a function from the set of variables that are already
  // bound to a type.

  case class Dom[S](apply: Set[String] => (S, Status[Tree]))
      extends Domain[S] {
    def get: (S, Status[Tree]) = apply(globalTypes.keySet)
  }

  def mapDom[T]
    (obj: Domain[T], globalNames: Set[String])
    (f: Tree => (T, Status[Tree])):
      (T, Status[Tree]) =
    obj match {
      case Dom(info) =>
        val (log, result) = info(globalNames)
        result match {
          case earlyFailure @ Failure(_) => (log, earlyFailure)
          case Success(τ) => f(τ)
        }
    }

  def inject[T](payload: T, τ: Status[Tree]) = Dom[T](_ => (payload, τ))

  def postulates[T]:
      T => PartialFunction[String, Domain[T]] =
    nil =>
    primitiveType.andThen[Domain[T]](τ => inject(nil, Success(τ)))

  def inferType[T]:
      PartialFunction[TreeF[Domain[T]], Tape => T => Domain[T]] = {

    // (→∀I)
    case ⊹:(AnnotatedAbstraction, arg, body) =>
      tape => payload => Dom[T] { globalNames =>
        mapDom(arg, globalNames) { σ =>
          val toQuantify = σ.freeNames -- globalNames
          mapDom(body, globalNames ++ toQuantify) { τ =>
            ( payload,
              Success(→(σ, τ).boundBy(toQuantify.map(
                α => BinderSpec(Universal, α, Annotation.none())
              )(collection.breakOut)))
            )
          }
        }
      }

    // (→∀∃E)
    case ⊹:(Application, fun, arg) =>
      tape => payload => Dom[T] { globalNames =>
        mapDom(fun, globalNames) { funType =>
          mapDom(arg, globalNames) { argType =>
            (payload, resultType(funType, argType, tape))
          }
        }
      }

    // Ascription
    case ⊹:(Ascription, actual, expected) =>
      tape => payload => Dom[T] { globalNames =>
        mapDom(actual, globalNames) { actualType =>
          mapDom(expected, globalNames) { expectedType =>
            if (mayAscribe(actualType, expectedType))
              (payload, Success(expectedType))
            else
              (payload, Failure(
                ascriptionFailure(expectedType, actualType)))
          }
        }
      }
  }

  def mayAscribe(from: Tree, to: Tree): Boolean = {
    // don't have to worry about capturing here,
    // it's a one-shot deal
    val ⊥ = æ(Subscript.newName("⊥", from.freeNames ++ to.freeNames))
    resultTypeCaptureNone(→(to, ⊥), from).toBoolean
  }

  // BLIND INFERENCE TRIALS FOR TESTING

  def resultTypeCaptureNone(funType: Tree, argType: Tree): Status[Tree] =
    resultType(funType, argType, Deterministic.allZeros)

  def resultTypeCaptureAll(funType: Tree, argType: Tree): Status[Tree] =
    resultType(funType, argType, Deterministic.allOnes)

  // TYPE INFERENCE GIVEN A NONDETERMINISTIC TAPE

  def resultType(funType: Tree, argType: Tree, tape: Tape): Status[Tree] =
  {
    // make sure fresh names in fun & arg do not clash
    val Seq(pf, px) = Prenex(funType, argType)

    // extract quantifiers from operator type,
    // rule out absurd operator types at the same time
    val (all_f, ex_f, σ0, τ0) = pf match {
      // operator is absurd, result is equally absurd
      case Prenex(_, æ(α)) if pf.isUniversal(α) =>
        return Success(∀(α, Annotation.none(), æ(α)))
      // if operator is not absurd then it must be function type
      case Prenex(prefix, σ → τ) =>
        val (all, ex) = prefix.partition(_.tag == Universal)
        (all, ex, σ, τ)
      case _ =>
        return Failure(s"nonfunction in operator position")
    }

    // extract quantifiers from operand type.
    val (all_x, ex_x, σ1) = px.blindPartition

    // order names in order of appearances
    val index = indexTypeVars(→(→(σ0, τ0), σ1))

    // collect quantified names based on quantifiers
    val all = collectNames(all_f, all_x)
    val  ex = collectNames( ex_f,  ex_x)

    // unification
    val monoMGS = unifyMonotypesBy(index, all, σ0, σ1) match {
      case Success(mgs) => mgs
      case Failure(msg) => return Failure(msg)
    }

    // question: should we consider occurrences in the result type?
    // answer: don't worry, that won't happen.
    //         any type variable not free in τ can't be captured.
    //
    // question: what about existentials? can they be captured?
    // answer: yes. not capturing yields a uniform existential,
    //         while capture could produce some universals or
    //         even more existentials.
    //
    // thus we use the DIVided EXistential form to compute depth
    // and count, but quantify over everything again at the end.
    val divex = →(σ0, Prenex.close(ex_f.toSeq, τ0))
    val depth = maxDepth  (divex, px.body)
    val count = totalCount(divex, px.body)

    val finalMGS = captureBy(index, all, ex, depth, count, monoMGS, tape)

    // trust monotype unification; there isn't more to test.

    Success(Prenex.close(pf.prefix ++ px.prefix, τ0 subst finalMGS))
  }

  def maxDepth(types: Tree*): String => Int =
    α => types.map(τ => Prenex.depth(α, τ)).max

  def totalCount(types: Tree*): String => Int =
    α => types.map(τ => Prenex.count(α, τ)).fold(0)(_ + _)

  // maps names of type variables to their location in a tree
  def indexTypeVars(τ: Tree): Map[String, Int] =
    τ.preorder.zipWithIndex.foldLeft(Map.empty[String, Int]) {
      case (acc, (æ(α), i)) if ! acc.contains(α) =>
        acc.updated(α, i)
      case (acc, _) =>
        acc
    }

  // collect names bound in binderspecs into a set
  def collectNames(prefixes: Seq[BinderSpec]*): Set[String] =
    prefixes.flatMap(_.map(_.x))(collection.breakOut)

  // INCARCERATION OF EXISTENTIALS & UNIVERSALS

  def captureBy(
    index   : String => Int,
    all     : Set[String],
    ex      : Set[String],
    depth   : String => Int,
    count   : String => Int,
    monoMGS : Map[String, Tree],
    tape    : Tape):
      Map[String, Tree] = {
    // process keys in sequence, s.t. tape makes sense
    val keys = monoMGS.keySet.toList.sortBy(index)
    keys.map(α => {
      val τ0 = monoMGS(α)
      val freebies = τ0.freeNames.filter(β => all(β) || ex(β)).
        toList.sortBy(index)
      val τ1 = freebies.foldLeft(τ0) {
        // β can be captured
        case (τ, β) if count(β) == Prenex.count(β, τ) =>
          // read the nondeterministic tape to see if we should
          // really capture β
          if (tape.read) {
            // let's capture β!
            val depthIn  = Prenex.depth(β, τ0)
            val depthOut = depth(β)
            assert(depthIn  >= 0)
            assert(depthOut >= 0)
            val paritiesAgree    = depthIn % 2 == depthOut % 2
            val paritiesDisagree = ! paritiesAgree
            if (paritiesAgree    && all.contains(β) ||
                paritiesDisagree &&  ex.contains(β))
              ∀(β, Annotation.none(), τ)
            else
              ∃(β, Annotation.none(), τ)
          }
          else
            // tape says we shan't capture β
            τ
        // β can't be captured
        case (τ, β) =>
          τ
      }
      (α, τ1)
    })(collection.breakOut)
  }
}

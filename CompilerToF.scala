trait CompilerToF
extends SystemMF
   with SystemF
   with AllNames
{
  import SystemF._

  implicit class CompilerFromSMFToF(smf: SMFTerm) {
    def toSystemF: FTerm = {
      val namesInSMF = getAllNames(smf.canon)

      val nameGenerator = new GenerativeNameGenerator(
        readableName("x"),
        x => (namesInSMF contains x) || smf.Γ.isDefinedAt(x)
      )

      val argTypes = collection.mutable.Map.empty[Name, Type]
      val Γ = argTypes orElse smf.Γ

      def loop(t: Term, boundTypeVars: Set[Name]): Term = t match {
        case χ(name) =>
          χ(name)

        case λ(name, body) =>
          val σ = smf.Γ(name)
          val quantifiedNames = getFreeNames(σ) -- boundTypeVars
          val realBody = loop(body, boundTypeVars ++ quantifiedNames)
          Λ(quantifiedNames)(λ(name, realBody))

        case ε(operator, operand) =>
          val s = loop(operator, boundTypeVars)
          val t = loop(operand , boundTypeVars)
          val operatorType = getSystemFType(s, Γ)
          val operandType  = getSystemFType(t, Γ)
          val TypeArgs4App(sTypeArgs, tTypeArgs, survivors, forbidden) =
            getTypeArgsInApp(operatorType, operandType)
          val resultType = doTypeApp(operatorType, sTypeArgs) match {
            case σ → τ => τ
          }
          val argQList = argumentQuantificationList(resultType)
          val etaBody =
            □(s, sTypeArgs) ₋
            Λ(forbidden)(□(t, tTypeArgs))
          val (result, additionalArgTypes) =
            etaExpandAndQuantify(etaBody, survivors, argQList, nameGenerator)
          argTypes ++= additionalArgTypes
          result
      }

      FTerm(loop(smf.canon, Set.empty), Γ, smf.names)
    }

    private[this]
    def readableName(default: String): Int => Name =
      index => s"${default}${if (index < 0) "_" else ""}${Math abs index}"
  }

  /** @param body        Term to η-expand
    * @param toQuantify  Names to quantify at the first opportunity
    * @param argQList    `argumentQuantificationList` of the type of body
    * @param newName     Name generator for η variables
    *
    * @return (result-of-η-expansion, argument-type-annotations)
    */
  def etaExpandAndQuantify(body: Term, toQuantify: Set[Name],
                           argQList: List[(Seq[Name], Type)],
                           newName: GenerativeNameGenerator):
      (Term, collection.Map[Name, Type]) = {
    val stillToQuantify = collection.mutable.Set.empty[Name] ++ toQuantify
    val argQs                 = argQList.init
    val (resultQ, resultType) = argQList.last

    def unsafeGetNewQuantifiers(
          preexistingQuantifiers: Seq[Name],
          typeBody: Type
    ): Seq[Name] = {
      stillToQuantify --= preexistingQuantifiers
      val quantifyHere = stillToQuantify & getFreeNames(typeBody)
      stillToQuantify --= quantifyHere
      quantifyHere.toSeq
    }

    // Invariant:
    //
    //   inner : ∀ quantifiers . argType → someOtherType
    //
    val (outer, inner): (Seq[(Seq[Name], Name, Type)], Term) =
      argQs.foldLeft((Seq.empty[(Seq[Name], Name, Type)], body)) {
        case ((outer, inner), (quantifiers, argType)) =>
          val x = newName.next
          val newQuantifiers = unsafeGetNewQuantifiers(quantifiers, argType)
          // new quantifiers are added inside the old ones
          val newOuter = outer :+ (
            (quantifiers ++ newQuantifiers, x, argType)
          )
          val newInner = □(inner, quantifiers map α) ₋ χ(x)
          (newOuter, newInner)
      }

    val newInner = Λ(unsafeGetNewQuantifiers(resultQ, resultType))(inner)

    val result = outer.foldRight(newInner) {
      case ((quantifiers, x, _), body) =>
        Λ(quantifiers)(λ(x, body))
    }

    val argTypes: Map[Name, Type] = outer.map({
      case (_, x, xType) => (x, xType)
    })(collection.breakOut)

    (result, argTypes)
  }

  /** @param forbidden  See `SystemMF.getMGS4App`. */
  case class TypeArgs4App(operatorTypeArgs: List[Type],
                          operandTypeArgs : List[Type],
                          toBeQuantified  : Set[Name],
                          forbidden       : Seq[Name])

  // Duplicates type checker and has hacks. Refactor?
  /** @return (operator-type-arguments, operand-type-arguments) */
  def getTypeArgsInApp(operatorType : Type, operandType  : Type):
      TypeArgs4App = {
    case class ID(index: Int) extends SecretLocalName
    val nameGenerator = new GenerativeNameGenerator(ID)

    val (listB, innerOperatorType) = listOfQuantifiers(operatorType)
    innerOperatorType match {
      case α(name) if listB == List(name) =>
        TypeArgs4App(List(operandType →: ∀("α")("α")), Nil,
                     Set.empty, Seq.empty)

      case _ =>
        val (sigma → tau0)  = innerOperatorType
        val (listA, sigma0) = listOfQuantifiers(sigma)
        val (listC, sigma1) = listOfQuantifiers(operandType )
        // Assume type checker figures out that listA, listB have
        // no common name and each list has unique names.
        val Seq(setA, setB, setC) = Seq(listA, listB, listC) map {
          list: List[Name] => list.toSet[Name]
        }
        val (namesA, substA) = getReplacement(setA, nameGenerator)
        val (namesB, substB) = getReplacement(setB, nameGenerator)
        val (namesC, substC) = getReplacement(setC, nameGenerator)
        val substAB = substA ++ substB
        val σ0 = sigma0 rename substAB
        val σ1 = sigma1 rename substC
        val MGS4App(typeAppsB, typeAppsC, survivors, forbidden) =
          getMGS4App(namesA, namesB, namesC, σ0, σ1)
        val τ  = tau0 rename substAB substitute typeAppsB
        val (invBC, _) =
          substC.foldRight(
            substB.inverse,
            substB.keySet ++ getFreeNames(τ)) {
            case ((nameC, idC), (acc, toAvoid)) =>
              val newNameC = getFreshName(nameC, toAvoid)
              (acc.updated(idC, newNameC), toAvoid + newNameC)
          }

        def listToTypeArgs(
              list    : List[Name],
              subst   : Map[Name, Name],
              typeArgs: Map[Name, Type]
        ): List[Type] = list map {
          name => typeArgs.withDefault(
            x => α(x)
          )(subst(name)).substitute(
            invBC.map({ case (id, name) => (id, α(name)) })
          )
        }

        TypeArgs4App(
          listToTypeArgs(listB, substB, typeAppsB),
          listToTypeArgs(listC, substC, typeAppsC),
          survivors map invBC,
          listA map (substA andThen forbidden andThen substC.inverse)
        )
    }
  }
}

object TestCompilerToF
extends CompilerToF
   with SystemMFExamples
   with PrettyF
{
  def main(args: Array[String]) {
    listOfSystemMFExamples foreach {
      example => println() ; println(pretty(example.toSystemF))
    }
  }
}

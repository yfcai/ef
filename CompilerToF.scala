trait CompilerToF
extends SystemMF
   with SystemF
   with AllNames
{
  import SystemF._

  implicit class CompilerFromSMFToF(smf: SMFTerm) {
    def toSystemF: FTerm = {
      val namesInSMF = getAllNames(smf.canon)

      val newName = new GenerativeNameGenerator(
        readableName("x"),
        x => (namesInSMF contains x) || smf.Γ.isDefinedAt(x)
      )

      val argTypes = collection.mutable.Map.empty[Name, Type]

      def loop(t: Term, boundTypeVars: Set[Name]): Term = t match {
        case χ(name) =>
          χ(name)

          case λ(name, body) =>
            val σ = smf.Γ(name)
            val quantifiedNames = getFreeNames(σ) -- boundTypeVars
            val realBody = loop(body, boundTypeVars ++ quantifiedNames)
            Λ(quantifiedNames)(realBody)

        case ε(operator, operand) =>
          val s = loop(operator, boundTypeVars)
          val t = loop(operand , boundTypeVars)
          val operatorType = smf.typeOfSubterm(operator, boundTypeVars)
          val operandType  = smf.typeOfSubterm(operand , boundTypeVars)
          val TypeArgs4App(sTypeArgs, tTypeArgs, survivors) =
            getTypeArgsInApp(operatorType, operandType)
          val etaBody = □(s, sTypeArgs) ₋ □(t, tTypeArgs)
          ???
      }

      FTerm(loop(smf.canon, Set.empty), argTypes orElse smf.Γ, smf.names)
    }

    private[this]
    def readableName(default: String): Int => Name =
      index => s"${default}${if (index < 0) "_" else ""}${Math abs index}"
  }

  case class TypeArgs4App(operatorTypeArgs: List[Type],
                          operandTypeArgs : List[Type],
                          toBeQuantified  : Set[Name])

  // Duplicates type checker and has hacks. Refactor?
  /** @return (operator-type-arguments, operand-type-arguments) */
  def getTypeArgsInApp(operatorType : Type, operandType  : Type):
      TypeArgs4App = {
    case class ID(index: Int) extends SecretLocalName
    val nameGenerator = new GenerativeNameGenerator(ID)

    val (listB, innerOperatorType) = listOfQuantifiers(operatorType)
    innerOperatorType match {
      case α(name) if listB == List(name) =>
        TypeArgs4App(List(operandType →: ∀("α")("α")), Nil, Set.empty)

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
        val MGS4App(typeAppsB, typeAppsC, survivors) =
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
          survivors map invBC
        )
    }
  }
}

object TestCompilerToF
extends CompilerToF
   with SystemMFExamples
{
  def main(args: Array[String]) {
    println(constId.toSystemF)
  }
}

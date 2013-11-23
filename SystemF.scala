trait SystemMF
extends TypedTerms with MinimalQuantification with Substitution
{
  case class SMFTerm(
    t: Term,
    Γ: PartialFunction[Name, Type],
    nameScheme: Map[Name, Name]
  )
  extends TypedTerm {
    def getTerm: Term = t
    def getType: Type = ???
  }
}

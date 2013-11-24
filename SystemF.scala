trait SystemMF
extends TypedTerms with MinimalQuantification with Substitution
{
  case class SMFTerm(
    canon: Term,
    Γ    : PartialFunction[Name, Type],
    names: Map[Name, Name]
  )
  extends TypedTerm {
    def getTerm: Term = canon renameAll names
    def getType: Type = ???
  }
}

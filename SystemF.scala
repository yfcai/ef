trait SystemMF extends MinimalQuantification with Substitution {
  case class SMFTerm(
    t: Term,
    Γ: PartialFunction[Name, Type],
    nameScheme: Map[Name, Name]
  )
}

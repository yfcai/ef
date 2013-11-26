trait SystemF extends TypedTerms {
  object SystemF {
    case class Λ(alpha: Name, body: Term) extends Term
    case class □(term: Term, typeArg: Type) extends Term
  }
}

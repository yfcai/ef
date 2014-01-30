trait Status {
  // Scala monadic programming:
  // Use this at the end of for-comprehension to circumvent the
  // mandatory return.
  //
  // Example: get result type of a term in operator position
  //
  // for {
  //   functionType <- getType(Γ, operator)
  //   _ <- NoReturn
  // } yield functionType match {
  //   case σ → τ =>
  //     Success(τ)
  //   case ω =>
  //     Failure(s"want function, got ${ω.unparse}")
  // }
  //
  object NoReturn {
    def map[T](f: Unit => T): T = f(())
  }

  trait Status[+T] {
    def toBoolean: Boolean
    def get: T
    def map[R](f: T => R): Status[R]
    def flatMap[R](f: T => Status[R]): Status[R]
  }

  case class Success[+T](get: T) extends Status[T] {
    def toBoolean: Boolean = true
    def map[R](f: T => R): Status[R] = Success(f(get))
    def flatMap[R](f: T => Status[R]): Status[R] = f(get)
  }

  case class Failure[+T](message: String) extends Status[T] {
    def toBoolean: Boolean = false
    def map[R](f: T => R): Status[R] = Failure(message)
    def flatMap[R](f: T => Status[R]): Status[R] = Failure(message)

    def get: T = sys error s"get of $this"
  }
}

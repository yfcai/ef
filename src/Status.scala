trait Status {
  trait Status[+T] {
    def toBoolean: Boolean
    def get: T
    def map[R](f: T => R): Status[R]
  }

  case class Success[+T](get: T) extends Status[T] {
    def toBoolean: Boolean = true
    def map[R](f: T => R): Status[R] = Success(f(get))
  }

  case class Failure[+T](message: String) extends Status[T] {
    def toBoolean: Boolean = false
    def map[R](f: T => R): Status[R] = Failure(message)

    def get: T = sys error s"get of $this"
  }
}

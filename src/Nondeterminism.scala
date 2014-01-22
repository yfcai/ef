/** Nondeterminism tape of a Turing machine */
trait Nondeterminism {
  topLevel =>

  trait Tape extends Iterator[Tape] {
    def readable: Boolean
    def read: Boolean
  }

  object Nondeterministic {
    def tape: Tape = (new Nondeterministic).tape
  }

  object Deterministic {
    def allZeros = Tape(Stream.continually(false))
    def allOnes  = Tape(Stream.continually(true ))

    case class Tape(var stream: Seq[Boolean]) extends topLevel.Tape {
      def hasNext: Boolean = false
      def next: Tape = sys error s"No next for a deterministic tape"

      def readable: Boolean = ! stream.isEmpty

      def read: Boolean = {
        val result = stream.head
        stream = stream.tail
        result
      }
    }
  }

  // possible optimization: prefix-skipping tape

  private
  class Nondeterministic {
    nondeterministic =>

    def maxQueries = 15 // can be overridden in subclasses

    type State = Int
    if (maxQueries > 32)
      sys error s"$maxQueries bit nondeterministic overflows Int state"

    var state: State = -1
    var hasNext: Boolean = true

    def tape: Tape = Tape(state)

    def nextTape: Tape = {
      state += 1
      hasNext = false
      Tape(state)
    }

    class OutOfTapeException
        extends Exception("$maxQuery bit of nondeterminism's used up")

    case class Tape(var i: Int, var j: Int = 0)
        extends topLevel.Tape {
      def nextQueryNumber: Int = j + 1

      def hasNext: Boolean = nondeterministic.hasNext

      def next: Tape = {
        val Tape(_i, _j) = nondeterministic.nextTape
        i = _i
        j = _j
        this
      }

      def readable: Boolean = nextQueryNumber <= maxQueries

      def read: Boolean = {
        if (! readable) throw new OutOfTapeException
        val result = 0 != (i & (1 << j))
        j += 1
        // if ever a bit 0 is consumed,
        // then there's a point to try a new tape.
        // if only 1s are produced,
        // then we've tried everything worth trying.
        if (result == false)
          nondeterministic.hasNext = true
        result
      }
    }
  }
}

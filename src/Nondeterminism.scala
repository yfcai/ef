/** Nondeterminism tape of a Turing machine */
trait Nondeterminism {
  topLevel =>

  trait Tape extends Iterator[Tape] {
    def readable: Boolean
    def read: Boolean

    def ZERO = true
    def ONE  = false

    // read an integer between 0 and n - 1
    // (wastes at most half the bits)
    def readInt(n: Int): Int = {
      val nextPowerOf2 = ceilLog2(n)
      val bits = (1 to nextPowerOf2).map(_ => read)
      val int = fromBinary(bits)
      if (int < n)
        int
      else
        n - 1
    }

    def ceilLog2(n: Int): Int =
      32 - java.lang.Integer.numberOfLeadingZeros(n - 1)

    def floorLog2(n: Int): Int =
      31 - java.lang.Integer.numberOfLeadingZeros(n)

    def fromBinary(bits: Iterable[Boolean]): Int =
      bits.foldLeft(0) {
        case (acc, bit) =>
          (acc << 1) + (if (bit == ONE) 1 else 0)
      }
  }

  object Nondeterministic {
    def tape: Tape = (new Nondeterministic).tape
  }

  object Deterministic {
    // anachronism... zero & one's meanings have been swapped.
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

  object DepthFirstSearch {
    def tape: DepthFirstSearch = DepthFirstSearch(0, Nil)
  }

  case object CarryBitSet extends Exception("carry bit set")

  case class DepthFirstSearch(
    var backtrack: Int,
    var log: List[Boolean]
  ) extends Tape {
    // can always read a DFS tape, it just takes forever sometimes
    def readable: Boolean = true

    // starting point of next iteration
    def prefix: List[Boolean] = log.drop(backtrack)

    def hasNext: Boolean = prefix.contains(ZERO)
    def next(): Tape = {
      increment()
      rewind()
      this
    }

    def rewind() { backtrack = log.length }

    def read: Boolean =
      if (backtrack > 0) {
        backtrack -= 1
        val result = log(backtrack)
        result
      }
      else {
        log = ZERO :: log
        ZERO
      }

    def increment() {
      log = increment(prefix)
    }

    def increment(input: List[Boolean]): List[Boolean] = input match {
      case bit :: bits =>
        if (bit == ZERO)
          ONE :: bits
        else
          ZERO :: increment(bits)
      case Nil =>
        throw CarryBitSet
    }
  }
}

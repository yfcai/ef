trait Names extends Flags {
  abstract class NameGenerator(avoid: Set[String] = Set.empty) {
    def mkName(prefix: String, index: Int): String

    def next: String = newName("_", Set("_"))

    def prefix(name: String): String = name

    def newName(toAvoid: Set[String]): String =
      newName("", toAvoid)

    def startingID(default: String) = -1

    def newName(default: String, toAvoid: Set[String]): String = {
      val v = avoid ++ toAvoid
      val p = prefix(default)
      val s = startingID(default)
      var x = p
      var i = s
      while (v contains x) {
        i = i + 1
        if (i == s) sys error "ran outta names"
        x = mkName(p, i)
      }
      x
    }

    def newNames(defaults: Seq[String], toAvoid: Set[String]): List[String] =
      defaults.foldLeft[(List[String], Set[String])]((Nil, toAvoid))({
        case ((nameList, toAvoid), name) =>
          val x = newName(name, toAvoid)
          (x :: nameList, toAvoid + x)
      })._1.reverse
  }

  /** subscript utilities */
  object Subscript extends Subscript(Set.empty)

  object Postscript extends Subscript() {
    override def s = "0123456789"
  }

  class Subscript(avoid: Set[String] = Set.empty)
      extends NameGenerator(avoid) {
    // Subscript.s
    def s =
      if (I_hate_unicode) "0123456789"
      else "₀₁₂₃₄₅₆₇₈₉"

    def is(c: Char): Boolean = s contains c

    override def prefix(subscribedName: String): String = {
      val j = subscribedName.lastIndexWhere(c => ! is(c))
      if (j >= 0)
        subscribedName.substring(0, j + 1)
      else
        subscribedName
    }

    def apply(i: Int): String = i.toString map (c => s(c - '0'))

    def mkName(prefix: String, index: Int): String =
      prefix + apply(index)
  }

  /** purely generative name generator */
  class GlobalNameGenerator(prefix: String) {
    var i: Int = 0
    def reset() { i = 0 }
    def next: String = {
      val result = s"$prefix%X".format(i)
      i += 1
      result
    }
  }

  object ABCSong extends ABCSong(Set.empty)

  class ABCSong(avoid: Set[String]) extends NameGenerator {
    var _i = 0
    override def startingID(default: String) = _i

    def umlauts =
      if (I_hate_unicode)
        "$!#%@^"
      else
        "äëïöüû"
    def lyrics = "abcdefghijklmnopqrstuvwxyz" + umlauts

    assert(lyrics.length == (1 << 5))

    def mkName(prefix: String, index: Int): String = {
      _i = index
      List(
        (index & ( 3 << 30)) >>> 30,
        (index & (31 << 25)) >>> 25,
        (index & (31 << 20)) >>> 20,
        (index & (31 << 15)) >>> 15,
        (index & (31 << 10)) >>> 10,
        (index & (31 <<  5)) >>>  5,
        (index &  31 )).
        flatMap(i => if (i == 0) None else Some(lyrics(i - 1))).mkString
    }
  }
}

scalaVersion := "2.10.2"

scalacOptions := Seq("-deprecation", "-feature", "-unchecked", "-Xlint")

libraryDependencies <+= scalaVersion("org.scala-lang" % "jline" % _ )

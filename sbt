#!/bin/bash
#
# http://stackoverflow.com/a/13474580
#
export JAVA_OPTS="-Dscalac.patmat.analysisBudget=512"
exec sbt

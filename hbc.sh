#!/bin/bash

IN="$@"
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
TMP="${DIR}/tmp.lc"
LCD="${DIR}/../mil"
CLASSPATH="${LCD}/bin"

"${DIR}/alb" --Sc "${IN}" -o "${TMP}" && java -cp "${CLASSPATH}" lc.LCC -S "${TMP}"

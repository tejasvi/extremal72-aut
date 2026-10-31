#!/bin/bash
# strip timing fields from csp5p / gtestS output lines
sed -E 's/ (wall|cpu|prep|t|tV3|tFP|tAT|tEXT)=[0-9.]+s?//g' "$@"

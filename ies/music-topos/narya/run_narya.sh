#!/bin/bash
# Wrapper to run narya with the narya53 opam switch
eval $(opam env --switch=narya53 --set-switch) && narya "$@"

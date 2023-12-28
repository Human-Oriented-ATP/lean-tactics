#!/usr/bin/env bash

SECONDS=0
PROJECT=${PWD##*/}
echo "Starting building $PROJECT." | logger -t lean4web

# Operate in the directory where this file is located
cd $(dirname $0)

lake exe cache get
lake build
# build the discrimination tree cache for library search
lake exe discrTrees

duration=$SECONDS
echo "Finished $PROJECT in $(($duration / 60)):$(($duration % 60)) min."
echo "Finished $PROJECT in $(($duration / 60)):$(($duration % 60)) min." | logger -t lean4web

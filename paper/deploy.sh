#!/bin/bash

rsync -aq --delete --exclude=.git --exclude=obj/* --exclude=bin/polytime-cpp \
      --exclude=paper/skeletons-input --exclude=paper/skeletons-output \
      --exclude=paper/input --exclude=paper/output \
      --exclude=paper/summary \
      ~/Devel/Phylogeny/ptime-persistent-phylogeny ppp:/data/

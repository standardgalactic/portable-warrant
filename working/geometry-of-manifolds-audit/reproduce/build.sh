#!/bin/bash
export ELAN_HOME=/home/claude/leanenv/elan PATH=/home/claude/leanenv/elan/bin:$PATH
cd /home/claude/leanenv/atlas-v1
echo "BUILD_START $(date)"
lake build Atlas.GeometryOfManifolds.GeometryOfManifolds > /home/claude/leanenv/build.full.log 2>&1
echo "BUILD_EXIT $? $(date)"

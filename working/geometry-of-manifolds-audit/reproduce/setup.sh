#!/bin/bash
export ELAN_HOME=/home/claude/leanenv/elan PATH=/home/claude/leanenv/elan/bin:$PATH
cd /home/claude/leanenv/atlas-v1
echo "START $(date)"; lean --version
lake exe cache get 2>&1 | tail -40
echo "CACHE_DONE $(date)"

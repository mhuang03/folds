#!/bin/bash
# N = 30, 31: u64 words, two moduli (2^64 and 2^61-1), combined by CRT in analyse.py
cd "$(dirname "$0")"
bash runall.sh 30 31 0 3
bash runall.sh 30 31 2305843009213693951 3

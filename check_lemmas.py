#!/usr/bin/env python3
import re
from pathlib import Path

filepath = Path(r"D:\桌面\aesop\problems\verina_advanced_3_solved.lean")
content = filepath.read_text(encoding='utf-8')

# Find all lines with lemma or theorem
lines = content.split('\n')
for i, line in enumerate(lines, 1):
    if re.match(r'^(lemma|theorem)\s+', line):
        print(f"Line {i}: {line[:80]}")

print(f"\nTotal lines: {len(lines)}")

#!/usr/bin/env bash
set -euo pipefail

################################
# 1. 替换文件内容
################################

find . -type f \
  ! -path './.git/*' \
  -print0 \
| xargs -0 sed -i \
    -e 's/codetic/codetic/g' \
    -e 's/Codetic/Codetic/g'


################################
# 2. 先重命名【目录】里的 Codetic -> Codetic
################################

find . -type d -name "*Codetic*" -print0 \
| sort -rz \
| while IFS= read -r -d '' d; do
    new="${d//Codetic/Codetic}"
    if [[ "$d" != "$new" ]]; then
        mv "$d" "$new"
    fi
done


################################
# 3. 再重命名【文件】里的 Codetic -> Codetic
################################

find . -type f -name "*Codetic*" -print0 \
| sort -rz \
| while IFS= read -r -d '' f; do
    new="${f//Codetic/Codetic}"
    if [[ "$f" != "$new" ]]; then
        mv "$f" "$new"
    fi
done

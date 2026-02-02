#只保留被证明的题目的proof中出现的tmp_lemmas，其余全部删掉
import re
import os

log_path = '/data1/zzh/codetic/codes_for_theorem_library/passed_verified.txt'
theorems_dir = '/data1/zzh/codetic/Codetic/theorems/'

# 1. 扫描全文，提取所有出现的 tmp_lemma 编号作为白名单
with open(log_path, 'r') as f:
    whitelist = set(re.findall(r'tmp_lemma_(\d+)', f.read()))

print(f"白名单 ID 总数: {len(whitelist)}")

# 2. 遍历文件夹，不在白名单的 lemma_ 文件一律删除
count = 0
for file_name in os.listdir(theorems_dir):
    match = re.search(r'lemma_(\d+)\.lean', file_name)
    if match and match.group(1) not in whitelist:
        os.remove(os.path.join(theorems_dir, file_name))
        count += 1

print(f"清理完毕，删除了 {count} 个未在日志中被引用的文件。")
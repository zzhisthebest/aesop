#!/usr/bin/env python3
"""验证单个 Lean 文件"""
import json
import sys
import os
import time
from tqdm import tqdm
import psutil

from lean_verifier import LeanVerifier

def verify_single(lean_code):
    """验证单个 Lean 代码"""
    verifier = LeanVerifier(
        path_to_repl="/data1/zzh/repl_v4.25.0/.lake/build/bin/repl",
        path_to_mathlib="/data1/zzh/aesop"
    )
    verifier.initialize()
    response = verifier.verify_single(lean_code)
    print(response)
    result = verifier.parse_results([response])
    verifier.shutdown()
    
    return result

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("用法: python verify_single.py <lean_file>")
        sys.exit(1)
    
    with open(sys.argv[1], 'r') as f:
        code = f.read()
    
    result = verify_single(code)
    print(f"结果: {result}")
    print(f"✅ 成功" if result[0].get("is_valid_with_sorry") else "❌ 失败")

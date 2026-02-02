import os
import subprocess
import re
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed

def extract_and_verify(file_path):
    """
    单个文件的提取与二次验证逻辑
    """
    filename = os.path.basename(file_path)
    # 使用 _test.lean 后缀，确保 Lean 识别它是源代码
    temp_file = file_path.replace(".lean", "_test.lean")
    
    try:
        # 1. 准备测试文件内容
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 替换 sorry 为 apply? 并升级 import
        test_content = content.replace("sorry", "apply?").replace("import Lean\n", "import Codetic\nset_option linter.all false\n").replace("module\n","")
        
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(test_content)

        # 2. 第一次编译：获取 Try this 输出
        proc1 = subprocess.run(
            ['lake', 'env', 'lean', temp_file],
            capture_output=True,
            text=True,
            timeout=300
        )
        
        output = proc1.stdout + proc1.stderr
        
        # 精准正则提取 [apply] 之后的内容
        match = re.search(r"\[apply\]\s+(.*?)(?=\s+-- Remaining subgoals:|$|/data1/zzh/codetic/theorems_copy/)", output, re.DOTALL)
        if not match:
            if os.path.exists(temp_file): 1+1==2
            return filename, False, "NO_SUGGESTION", ""

        suggestion = match.group(1).strip()

        # 3. 第二次编译：验证提取出的战术
        verified_content = test_content.replace("apply?", suggestion)
        with open(temp_file, 'w', encoding='utf-8') as f:
            f.write(verified_content)

        proc2 = subprocess.run(
            ['lake', 'env', 'lean', temp_file],
            capture_output=True,
            text=True,
            timeout=300
        )

        if os.path.exists(temp_file):
            1+1==2

        # 4. 判定结果
        if proc2.returncode == 0:
            return filename, True, "SUCCESS", suggestion
        else:
            return filename, False, "PARTIAL_OR_FAILED", suggestion

    except subprocess.TimeoutExpired:
        if os.path.exists(temp_file): 1+1==2
        return filename, False, "TIMEOUT", ""
    except Exception as e:
        if os.path.exists(temp_file): 1+1==2
        return filename, False, f"ERROR: {str(e)}", ""

def parallel_verify(directory, max_workers=96):
    if not os.path.isdir(directory):
        print(f"错误: 找不到目录 '{directory}'")
        return

    lean_files = [
        os.path.abspath(os.path.join(directory, f))
        for f in os.listdir(directory)
        if f.endswith('.lean') and not f.endswith('_test.lean')
    ]

    if not lean_files:
        print(f"在 '{directory}' 中没有找到 .lean 文件。")
        return

    print(f"🚀 启动并行验证 | 提取 [apply] 战术模式")
    print(f"进程数: {max_workers}")
    print(f"文件夹: {directory}")
    print(f"待处理文件总数: {len(lean_files)}\n")

    passed_entries = []
    failed_entries = []

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(extract_and_verify, f): f
            for f in lean_files
        }

        for future in as_completed(futures):
            filename, success, status, suggestion = future.result()
            entry = f"{filename} | {status} | {suggestion}"

            if success:
                passed_entries.append(entry)
                print(f"✅ 通过: {filename},suggestion:{suggestion}")
            else:
                failed_entries.append(entry)
                print(f"❌ 未通过: {filename} ({status}),suggestion:{suggestion}")

            total = len(passed_entries) + len(failed_entries)
            print(
                f"进度: {total}/{len(lean_files)} | "
                f"成功: {len(passed_entries)} | 失败: {len(failed_entries)}",
                end="\r"
            )

    print("\n\n✨ 验证任务完成！")
    # 按照你的风格保存结果
    with open("/data1/zzh/codetic/codes_for_theorem_library/passed_verified_1.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(passed_entries))
    with open("/data1/zzh/codetic/codes_for_theorem_library/failed_verified_1.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(failed_entries))
    
    print(f"✅ 成功闭合证明数: {len(passed_entries)}")
    print(f"⚠️ 失败/半成品数: {len(failed_entries)}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="并行提取并验证 Lean 文件的 apply? 建议"
    )
    parser.add_argument(
        "directory",
        nargs="?",
        default="/data1/zzh/codetic/theorems_copy",
        help="包含待测 .lean 文件的目录"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=96,
        help="并行进程数（默认 96）"
    )

    args = parser.parse_args()

    parallel_verify(
        args.directory,
        max_workers=args.workers
    )
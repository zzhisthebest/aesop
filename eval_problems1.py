import os
import subprocess
import sys
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed

def check_and_maybe_delete(file_path, do_delete: bool):
    """
    单个文件的检查逻辑
    do_delete = True  -> 通过就删除
    do_delete = False -> 只检查，不删除
    """
    filename = os.path.basename(file_path)
    try:
        result = subprocess.run(
            ['lake', 'env', 'lean', file_path],
            capture_output=True,
            text=True,
            timeout=300
        )

        if result.returncode == 0:
            if do_delete:
                os.remove(file_path)
                return filename, True, "deleted"
            else:
                # 新增：通过的文件重命名为 _solvedByAesop
                dir_name = os.path.dirname(file_path)
                stem, ext = os.path.splitext(filename)
                new_name = f"{stem}_solvedByAesop{ext}"
                new_path = os.path.join(dir_name, new_name)

                if not os.path.exists(new_path):
                    os.rename(file_path, new_path)
                    return filename, True, f"renamed to {new_name}"
                else:
                    return filename, True, f"already exists {new_name}"
        else:
            return filename, False, result.stderr

    except subprocess.TimeoutExpired:
        return filename, False, "Timeout"
    except Exception as e:
        return filename, False, str(e)

def parallel_clean(directory, max_workers=96, do_delete=False):
    if not os.path.isdir(directory):
        print(f"错误: 找不到目录 '{directory}'")
        return

    lean_files = [
        os.path.abspath(os.path.join(directory, f))
        for f in os.listdir(directory)
        if f.endswith('.lean')
    ]

    if not lean_files:
        print(f"在 '{directory}' 中没有找到 .lean 文件。")
        return

    mode = "删除模式" if do_delete else "检查模式（不删除）"
    print(f"🚀 启动并行处理 | {mode}")
    print(f"进程数: {max_workers}")
    print(f"文件夹: {directory}")
    print(f"待处理文件总数: {len(lean_files)}\n")

    passed_count = 0
    failed_count = 0

    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(check_and_maybe_delete, f, do_delete): f
            for f in lean_files
        }

        for future in as_completed(futures):
            filename, success, info = future.result()

            if success:
                passed_count += 1
                if do_delete:
                    print(f"✅ 删除: {filename}")
                else:
                    print(f"✅ 通过: {filename}")
            else:
                failed_count += 1
                print(f"❌ 保留: {filename}")

            total = passed_count + failed_count
            print(
                f"进度: {total}/{len(lean_files)} | "
                f"通过: {passed_count} | 失败: {failed_count}",
                end="\r"
            )

    print("\n\n✨ 任务完成！")
    print(f"✅ 通过: {passed_count}")
    print(f"⚠️ 失败: {failed_count}")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="并行检查 Lean 文件，可选是否删除通过的文件"
    )
    parser.add_argument(
        "directory",
        nargs="?",
        default="/data1/zzh/aesop/problems1",
        help="包含 .lean 文件的目录"
    )
    parser.add_argument(
        "--delete",
        type=lambda x: x.lower() == "true",
        default=False,
        help="是否删除通过检查的 .lean 文件（true / false，默认 false）"
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=96,
        help="并行进程数（默认 96）"
    )

    args = parser.parse_args()

    parallel_clean(
        args.directory,
        max_workers=args.workers,
        do_delete=args.delete
    )

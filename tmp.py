import os
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed

def check_and_delete(file_path):
    """
    单个文件的检查逻辑：返回文件名和处理结果
    """
    filename = os.path.basename(file_path)
    try:
        # 执行 lake env lean
        result = subprocess.run(
            ['lake', 'env', 'lean', file_path],
            capture_output=True,
            text=True,
            timeout=300 # 设置 5 分钟超时，防止某些复杂证明卡死进程
        )

        if result.returncode == 0:
            os.remove(file_path)
            return filename, True, None
        else:
            return filename, False, result.stderr
    except subprocess.TimeoutExpired:
        return filename, False, "Timeout"
    except Exception as e:
        return filename, False, str(e)

def parallel_clean(directory, max_workers=96):
    if not os.path.isdir(directory):
        print(f"错误: 找不到目录 '{directory}'")
        return

    # 获取绝对路径，防止进程切换目录导致找不到文件
    lean_files = [os.path.abspath(os.path.join(directory, f)) 
                  for f in os.listdir(directory) if f.endswith('.lean')]
    
    if not lean_files:
        print(f"在 '{directory}' 中没有找到 .lean 文件。")
        return

    print(f"🚀 启动并行清理，进程数: {max_workers}")
    print(f"文件夹: {directory}")
    print(f"待处理文件总数: {len(lean_files)}")

    passed_count = 0
    failed_count = 0

    # 使用进程池进行处理
    with ProcessPoolExecutor(max_workers=max_workers) as executor:
        # 提交所有任务
        future_to_file = {executor.submit(check_and_delete, f): f for f in lean_files}
        
        for future in as_completed(future_to_file):
            filename, success, error = future.result()
            if success:
                passed_count += 1
                print(f"✅ 删除: {filename}")
                # 仅在成功时静默打印，或者你可以选择不打印
            else:
                failed_count += 1
                print(f"❌ 保留 (报错/超时): {filename}")
                # 如果需要调试，可以打印 error

            # 打印实时进度
            total_processed = passed_count + failed_count
            print(f"进度: {total_processed}/{len(lean_files)} | 已删除: {passed_count} | 保留: {failed_count}", end='\r')

    print(f"\n\n✨ 任务完成！")
    print(f"✅ 总计删除: {passed_count}")
    print(f"⚠️ 总计保留: {failed_count}")

if __name__ == "__main__":
    # 默认路径
    default_path = "/data1/zzh/aesop/problems1"
    target_dir = sys.argv[1] if len(sys.argv) > 1 else default_path
    
    # 进程数，根据你的要求设为 96
    num_processes = 96
    
    parallel_clean(target_dir, max_workers=num_processes)
import sys
sys.path.insert(0, '/data1/zzh/Lean-Mutation')
from utils.commands import *

# 读取文件
with open('/data1/zzh/aesop/lemmas_quickchecked_148.lean', 'r') as f:
    code = f.read()

# 启动 repl
process = run_env_build('/data1/zzh/aesop', '/data1/zzh/repl_v4.25.0', None)

# 发送代码
result = send_input_to_process(process,  {"cmd": code})
    
# 打印结果
print(result)
print(f"has_error: {result is False or any(m.get('severity') == 'error' for m in result.get('messages', []))}")
if result and 'messages' in result:
    for msg in result['messages']:
        if msg.get('severity') == 'error':
            print(f"ERROR at line {msg.get('pos', {}).get('line')}: {msg.get('data', '')[:100]}")

process.terminate()

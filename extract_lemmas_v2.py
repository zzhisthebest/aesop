#!/usr/bin/env python3
"""
Extract lemmas and have statements from Lean files - Version 2
Uses line-by-line scanning for better accuracy.
"""

import re
from pathlib import Path
from typing import List, Dict, Tuple

def find_statement_end(lines: List[str], start_idx: int) -> int:
    """
    Find the end of a lemma/theorem/have statement starting at start_idx.
    Returns the index of the last line of the statement.
    """
    depth = 0
    in_proof = False
    
    for i in range(start_idx, len(lines)):
        line = lines[i].rstrip()
        
        # Skip comments
        if line.strip().startswith('--'):
            continue
        
        # Check for 'by' to start proof
        if 'by' in line and not in_proof:
            in_proof = True
        
        # Track parentheses depth
        for char in line:
            if char in '({[⟨':
                depth += 1
            elif char in ')}]⟩':
                depth -= 1
        
        # Check for end of statement
        if in_proof and depth <= 0:
            # Look for next top-level declaration
            next_line = lines[i+1] if i+1 < len(lines) else ""
            if (re.match(r'^(lemma|theorem|def|example|end)\s+', next_line) or
                next_line.strip() == "" and i+2 < len(lines) and 
                re.match(r'^(lemma|theorem|def|example)', lines[i+2])):
                return i
        
        # Stop if we've gone too far (blank line followed by new declaration)
        if i > start_idx + 500:  # Safety limit
            return i
    
    return len(lines) - 1

def extract_from_file(filepath: Path) -> Tuple[List[Dict], List[Dict]]:
    """Extract lemmas and haves from a Lean file."""
    
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    lemmas = []
    haves = []
    
    # Find namespace
    namespace = ""
    for line in lines:
        match = re.match(r'namespace\s+([^\s]+)', line)
        if match:
            namespace = match.group(1)
            break
    
    print(f"Namespace: {namespace}")
    
    # Extract lemmas and theorems
    for i, line in enumerate(lines):
        # Match lemma or theorem declarations
        lemma_match = re.match(r'^(lemma|theorem)\s+([\w.]+)', line)
        if lemma_match:
            lemma_type = lemma_match.group(1)
            lemma_name = lemma_match.group(2)
            
            print(f"Found {lemma_type}: {lemma_name} at line {i+1}")
            
            # Find the end of this lemma
            end_idx = find_statement_end(lines, i)
            
            # Extract the full text
            full_text = ''.join(lines[i:end_idx+1]).strip()
            
            # Split into signature and proof
            # Find := or by
            if ':=' in full_text:
                parts = full_text.split(':=', 1)
                signature_part = parts[0].replace(f'{lemma_type} {lemma_name}', '').strip()
                proof_part = parts[1].strip()
            elif ' by' in full_text:
                parts = full_text.split(' by', 1)
                signature_part = parts[0].replace(f'{lemma_type} {lemma_name}', '').strip()
                proof_part = 'by' + parts[1]
            else:
                print(f"  Warning: Could not parse {lemma_name}")
                continue
            
            lemmas.append({
                'type': lemma_type,
                'name': lemma_name.split('.')[-1],
                'full_name': lemma_name,
                'signature': signature_part,
                'proof': proof_part,
                'line': i + 1
            })
    
    # Extract have statements
    for i, line in enumerate(lines):
        # Match have statements
        have_match = re.search(r'\bhave\s+([a-zA-Z_][\w\']*)\s*:', line)
        if have_match:
            have_name = have_match.group(1)
            
            # Skip anonymous haves
            if have_name in ['_', 'this']:
                continue
            
            print(f"Found have: {have_name} at line {i+1}")
            
            # Find the end (look for := and then the proof)
            end_idx = i
            found_assign = False
            
            # Scan forward to find :=
            for j in range(i, min(i+20, len(lines))):
                if ':=' in lines[j]:
                    found_assign = True
                    # Find end of proof (next statement or semicolon)
                    for k in range(j, min(j+50, len(lines))):
                        if (';' in lines[k] or 
                            re.search(r'^\s+(have|let|by|·)\s+', lines[k+1] if k+1 < len(lines) else "")):
                            end_idx = k
                            break
                    break
            
            if not found_assign:
                print(f"  Warning: No := found for {have_name}")
                continue
            
            # Extract the full text
            full_text = ''.join(lines[i:end_idx+1]).strip()
            
            # Remove trailing semicolon
            if full_text.endswith(';'):
                full_text = full_text[:-1].strip()
            
            # Parse into type and proof
            if ':=' in full_text:
                # Split at have name :
                type_match = re.search(rf'\bhave\s+{have_name}\s*:\s*(.+?)\s*:=(.+)', full_text, re.DOTALL)
                if type_match:
                    type_sig = type_match.group(1).strip()
                    proof = type_match.group(2).strip()
                    
                    # Find context (which lemma this have is in)
                    context = None
                    for j in range(i-1, -1, -1):
                        ctx_match = re.match(r'^(lemma|theorem)\s+([\w.]+)', lines[j])
                        if ctx_match:
                            context = ctx_match.group(2)
                            break
                    
                    haves.append({
                        'type': 'have',
                        'name': have_name,
                        'full_name': f"{namespace}_have_{have_name}_{len(haves)}",
                        'signature': type_sig,
                        'proof': proof,
                        'context': context,
                        'line': i + 1
                    })
    
    return lemmas, haves

def create_test_file(item: Dict, output_dir: Path, imports: str, namespace: str):
    """Create a test file for a lemma or have."""
    
    # Sanitize filename
    safe_name = item['name'].replace('.', '_').replace('/', '_')
    filename = f"{item['type']}_{safe_name}.lean"
    filepath = output_dir / filename
    
    # Build the test file content
    content = f"""/-
Extracted from verina_advanced_3_solved.lean
Type: {item['type']}
Original name: {item['full_name']}
Line: {item.get('line', '?')}
"""
    
    if item.get('context'):
        content += f"Context: Inside {item['context']}\n"
    
    content += """-/

"""
    
    content += imports
    content += "\n\n"
    
    if namespace:
        content += f"namespace {namespace}\n\n"
    
    # Add the lemma/theorem
    if item['type'] == 'have':
        # Convert have to lemma
        content += f"lemma {item['name']} : {item['signature']} := {item['proof']}\n"
    else:
        content += f"{item['type']} {item['name']} {item['signature']} := {item['proof']}\n"
    
    if namespace:
        content += f"\nend {namespace}\n"
    
    # Write the file
    filepath.write_text(content, encoding='utf-8')
    print(f"  Created: {filename}")

def main():
    source_file = Path(r"D:\桌面\aesop\problems\verina_advanced_3_solved.lean")
    output_dir = Path(r"D:\桌面\aesop\testLemmasAndHavesFromAristotle")
    
    # Create output directory
    output_dir.mkdir(exist_ok=True)
    
    # Read source file
    print(f"Reading {source_file}...\n")
    
    # Extract lemmas and haves
    lemmas, haves = extract_from_file(source_file)
    
    print(f"\n{'='*60}")
    print(f"Found {len(lemmas)} lemmas/theorems")
    print(f"Found {len(haves)} have statements")
    print(f"{'='*60}\n")
    
    # Get imports from source file
    with open(source_file, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    imports_lines = []
    for line in lines:
        if line.startswith('import ') or line.startswith('set_option '):
            imports_lines.append(line.rstrip())
        elif re.match(r'^(namespace|def|lemma|theorem)', line):
            break
    
    imports = '\n'.join(imports_lines[:5])  # Take first 5 import lines
    if not imports:
        imports = "import Mathlib\nimport Codetic"
    
    # Get namespace
    namespace = ""
    for line in lines:
        match = re.match(r'namespace\s+([^\s]+)', line)
        if match:
            namespace = match.group(1)
            break
    
    # Create test files
    print(f"Creating test files in {output_dir}...\n")
    
    created_count = 0
    for lemma in lemmas:
        try:
            create_test_file(lemma, output_dir, imports, namespace)
            created_count += 1
        except Exception as e:
            print(f"  Error creating file for {lemma['name']}: {e}")
    
    for have in haves:
        try:
            create_test_file(have, output_dir, imports, namespace)
            created_count += 1
        except Exception as e:
            print(f"  Error creating file for {have['name']}: {e}")
    
    print(f"\n{'='*60}")
    print(f"Done! Created {created_count} test files.")
    print(f"Lemmas: {len(lemmas)}, Have statements: {len(haves)}")
    print(f"{'='*60}")

if __name__ == "__main__":
    main()

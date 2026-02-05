#!/usr/bin/env python3
"""
Extract lemmas and have statements from Lean files and create individual test files.
"""

import re
import os
from pathlib import Path
from typing import List, Tuple, Dict

def find_matching_delimiter(text: str, start_pos: int, open_char: str = '(', close_char: str = ')') -> int:
    """Find the position of the matching closing delimiter."""
    count = 0
    i = start_pos
    while i < len(text):
        if text[i] == open_char:
            count += 1
        elif text[i] == close_char:
            count -= 1
            if count == 0:
                return i
        i += 1
    return -1

def extract_proof_block(text: str, start_pos: int) -> Tuple[str, int]:
    """
    Extract a proof block starting with 'by' at start_pos.
    Returns (proof_text, end_position).
    Handles nested 'by' blocks and various proof terminators.
    """
    if not text[start_pos:].lstrip().startswith('by'):
        return "", start_pos
    
    # Find the start of 'by'
    by_match = re.search(r'\bby\b', text[start_pos:])
    if not by_match:
        return "", start_pos
    
    by_start = start_pos + by_match.start()
    pos = by_start + 2  # Skip 'by'
    
    # Track nesting level
    depth = 0
    in_string = False
    in_comment = False
    
    # Common proof terminators at depth 0
    terminators = [
        '\nlemma ', '\ntheorem ', '\ndef ', '\nend ',
        '\n\nlemma ', '\n\ntheorem ', '\n\ndef ', '\n\nend ',
        '\nexample '
    ]
    
    while pos < len(text):
        char = text[pos]
        
        # Handle string literals
        if char == '"' and (pos == 0 or text[pos-1] != '\\'):
            in_string = not in_string
            pos += 1
            continue
        
        if in_string:
            pos += 1
            continue
        
        # Handle comments
        if text[pos:pos+2] == '/-':
            in_comment = True
            pos += 2
            continue
        
        if in_comment:
            if text[pos:pos+2] == '-/':
                in_comment = False
                pos += 2
            else:
                pos += 1
            continue
        
        if text[pos:pos+2] == '--':
            # Line comment, skip to end of line
            while pos < len(text) and text[pos] != '\n':
                pos += 1
            pos += 1
            continue
        
        # Track nesting with common delimiters
        if char in '({[⟨':
            depth += 1
        elif char in ')}]⟩':
            depth -= 1
        
        # Check for proof terminators at depth 0
        if depth <= 0:
            for term in terminators:
                if text[pos:pos+len(term)] == term:
                    return text[by_start:pos], pos
        
        pos += 1
    
    # End of file
    return text[by_start:], len(text)

def extract_lemmas(content: str, namespace: str = "") -> List[Dict]:
    """Extract all lemmas from the content."""
    lemmas = []
    
    # Pattern to match lemma/theorem declarations (more flexible)
    # Matches "lemma name" or "namespace.lemma name" or "private lemma name"
    # Allow dots in the name for qualified names like "verina_advanced_3.LCSLength"
    # Match from newline or start, with optional whitespace
    lemma_pattern = r'\n((?:private\s+)?(?:lemma|theorem))\s+((?:[a-zA-Z_][a-zA-Z0-9_\']*\.)*[a-zA-Z_][a-zA-Z0-9_\']*)\s+'
    
    matches = list(re.finditer(lemma_pattern, content, re.MULTILINE))
    
    print(f"Debug: Found {len(matches)} potential lemma/theorem matches")
    
    for i, match in enumerate(matches):
        lemma_type = match.group(1).strip()
        lemma_name = match.group(2)
        lemma_start = match.start()
        
        # Skip if the name contains 'namespace' (false positive)
        if 'namespace' in lemma_name.lower():
            continue
        
        print(f"Debug: Processing {lemma_type} {lemma_name}")
        
        # Find the signature (everything up to ':=' or 'by')
        sig_start = match.end()
        
        # Look for the type signature (up to := or by)
        pos = sig_start
        sig_end = pos
        depth = 0
        found_proof = False
        proof_text = ""
        
        while pos < len(content):
            char = content[pos]
            
            # Skip comments
            if content[pos:pos+2] == '/-':
                comment_end = content.find('-/', pos + 2)
                if comment_end != -1:
                    pos = comment_end + 2
                    continue
            
            if content[pos:pos+2] == '--':
                line_end = content.find('\n', pos)
                if line_end != -1:
                    pos = line_end + 1
                    continue
            
            if char in '({[⟨':
                depth += 1
            elif char in ')}]⟩':
                depth -= 1
            
            # Check for := or by at depth 0
            if depth == 0:
                if content[pos:pos+2] == ':=':
                    sig_end = pos
                    proof_start = pos + 2
                    
                    # Check if next non-whitespace is 'by'
                    after_assign = content[proof_start:].lstrip()
                    if after_assign.startswith('by'):
                        proof_text, _ = extract_proof_block(content, proof_start)
                    else:
                        # Term proof - find the end
                        # Look for next top-level definition
                        next_def = len(content)
                        for pattern in [r'\n(?:lemma|theorem|def|example|end)\s+', r'\n\n']:
                            m = re.search(pattern, content[proof_start:])
                            if m:
                                candidate = proof_start + m.start()
                                if candidate < next_def:
                                    next_def = candidate
                        
                        proof_text = content[proof_start:next_def].strip()
                    
                    found_proof = True
                    break
                    
                elif re.match(r'\s+by\b', content[pos:]):
                    sig_end = pos
                    proof_text, _ = extract_proof_block(content, pos)
                    found_proof = True
                    break
            
            pos += 1
            
            # Safety: stop if we've gone too far
            if pos - lemma_start > 10000:
                print(f"Warning: Stopped parsing {lemma_name} after 10000 chars")
                break
        
        if not found_proof:
            print(f"Warning: No proof found for {lemma_name}")
            continue
        
        signature = content[sig_start:sig_end].strip()
        
        # Clean up full name
        full_name = lemma_name
        if namespace and not lemma_name.startswith(namespace + '.'):
            full_name = f"{namespace}.{lemma_name}"
        
        lemmas.append({
            'type': lemma_type,
            'name': lemma_name.split('.')[-1],  # Get just the last part
            'full_name': full_name,
            'signature': signature,
            'proof': proof_text.strip(),
            'start_pos': lemma_start
        })
    
    return lemmas

def extract_haves(content: str, namespace: str = "") -> List[Dict]:
    """Extract all have statements from proofs."""
    haves = []
    
    # Pattern to match have statements
    # have NAME : TYPE := PROOF or have NAME : TYPE := by PROOF
    have_pattern = r'\bhave\s+([a-zA-Z_][a-zA-Z0-9_\']*)\s*:'
    
    matches = list(re.finditer(have_pattern, content))
    
    print(f"Debug: Found {len(matches)} potential have statements")
    
    for idx, match in enumerate(matches):
        have_name = match.group(1)
        have_start = match.start()
        
        # Skip patterns like "have : ..." without a name
        if have_name in ['_', 'this']:
            continue
        
        print(f"Debug: Processing have {have_name}")
        
        # Extract the type
        type_start = match.end()
        pos = type_start
        depth = 0
        type_end = pos
        found_proof = False
        proof_text = ""
        
        while pos < len(content):
            char = content[pos]
            
            # Skip comments
            if content[pos:pos+2] == '/-':
                comment_end = content.find('-/', pos + 2)
                if comment_end != -1:
                    pos = comment_end + 2
                    continue
            
            if content[pos:pos+2] == '--':
                line_end = content.find('\n', pos)
                if line_end != -1:
                    pos = line_end + 1
                    continue
            
            if char in '({[⟨':
                depth += 1
            elif char in ')}]⟩':
                depth -= 1
            
            # Look for := at depth 0
            if depth == 0 and content[pos:pos+2] == ':=':
                type_end = pos
                proof_start = pos + 2
                
                # Check if it's 'by' proof or term proof
                proof_start_stripped = content[proof_start:].lstrip()
                if proof_start_stripped.startswith('by'):
                    proof_text, proof_end = extract_proof_block(content, proof_start)
                else:
                    # Term proof - find the end
                    # Look for semicolon or next statement
                    term_end = proof_start
                    term_depth = 0
                    
                    while term_end < len(content):
                        if content[term_end] in '({[⟨':
                            term_depth += 1
                        elif content[term_end] in ')}]⟩':
                            term_depth -= 1
                        
                        # End markers at depth 0
                        if term_depth == 0:
                            # Check for statement terminators
                            if content[term_end] == ';':
                                term_end += 1
                                break
                            # Check for next have/let/match etc.
                            if re.match(r'\s*(?:have|let|match|by|·)\b', content[term_end:]):
                                break
                            # Check for blank line
                            if content[term_end:term_end+2] == '\n\n':
                                break
                        
                        term_end += 1
                        
                        if term_end - proof_start > 5000:
                            break
                    
                    proof_text = content[proof_start:term_end].strip()
                    # Remove trailing semicolon if present
                    if proof_text.endswith(';'):
                        proof_text = proof_text[:-1].strip()
                
                found_proof = True
                break
            
            pos += 1
            
            # Safety: stop if we've gone too far
            if pos - have_start > 5000:
                print(f"Warning: Stopped parsing have {have_name} after 5000 chars")
                break
        
        if not found_proof:
            print(f"Warning: No proof found for have {have_name}")
            continue
        
        type_sig = content[type_start:type_end].strip()
        
        # Try to determine context (which lemma/theorem this have is in)
        context_match = None
        for lemma_match in re.finditer(r'(?:^|\n)\s*(?:lemma|theorem)\s+([^\s:]+)', content[:have_start], re.MULTILINE):
            context_match = lemma_match.group(1)
        
        haves.append({
            'type': 'have',
            'name': have_name,
            'full_name': f"{namespace}.have_{have_name}_{idx}",
            'signature': type_sig,
            'proof': proof_text.strip(),
            'context': context_match,
            'start_pos': have_start
        })
    
    return haves

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
    print(f"Created: {filepath}")

def main():
    source_file = Path(r"D:\桌面\aesop\problems\verina_advanced_3_solved.lean")
    output_dir = Path(r"D:\桌面\aesop\testLemmasAndHavesFromAristotle")
    
    # Create output directory
    output_dir.mkdir(exist_ok=True)
    
    # Read source file
    print(f"Reading {source_file}...")
    content = source_file.read_text(encoding='utf-8')
    
    # Extract namespace
    namespace_match = re.search(r'\nnamespace\s+([^\s]+)', content)
    namespace = namespace_match.group(1) if namespace_match else ""
    print(f"Detected namespace: {namespace or 'none'}")
    
    # Extract imports (everything before the first namespace or def)
    imports_end = content.find('\nnamespace ')
    if imports_end == -1:
        imports_end = content.find('\ndef ')
    if imports_end == -1:
        imports_end = content.find('\nlemma ')
    
    imports = content[:imports_end].strip() if imports_end > 0 else "import Mathlib\nimport Codetic"
    
    # Extract lemmas and haves
    print("\nExtracting lemmas...")
    lemmas = extract_lemmas(content, namespace)
    print(f"Found {len(lemmas)} lemmas")
    
    print("\nExtracting have statements...")
    haves = extract_haves(content, namespace)
    print(f"Found {len(haves)} have statements")
    
    # Create test files
    print(f"\nCreating test files in {output_dir}...")
    
    for lemma in lemmas:
        try:
            create_test_file(lemma, output_dir, imports, namespace)
        except Exception as e:
            print(f"Error creating file for {lemma['name']}: {e}")
    
    for have in haves:
        try:
            create_test_file(have, output_dir, imports, namespace)
        except Exception as e:
            print(f"Error creating file for {have['name']}: {e}")
    
    print(f"\nDone! Created {len(lemmas) + len(haves)} test files.")
    print(f"Lemmas: {len(lemmas)}, Have statements: {len(haves)}")

if __name__ == "__main__":
    main()

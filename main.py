import os, sys

# helpers

def ask_source_path() -> str:
    while True:
        try:
            p = input("Введите путь к исходному .txt файлу: ").strip().strip('"')
        except (EOFError, KeyboardInterrupt):
            sys.exit("\nОтмена.")
        if not p or not os.path.isfile(p):
            print("Файл не найден. Попробуйте снова.")
            continue
        return p

def out_path(src: str) -> str:
    base, _ = os.path.splitext(src)
    return base + '.asm'

# lexing utils

def multi_split(s: str, seps):
    res, cur = [], ''
    for ch in s:
        if ch in seps:
            if cur.strip(): res.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip(): res.append(cur.strip())
    return res

# infix → postfix (RPN) and RPN → MASM

PRECEDENCE = {'||':1,'&&':2,'==':3,'!=':3,'<':3,'>':3,'<=':3,'>=':3,'+':4,'-':4,'*':5,'/':5,'%':5}

def infix_to_postfix(tokens):
    out, st, i = [], [], 0
    while i < len(tokens):
        tok = tokens[i]
        if i+1 < len(tokens) and tok+tokens[i+1] in PRECEDENCE:
            tok += tokens[i+1]; i += 1
        if tok == '(': st.append(tok)
        elif tok == ')':
            while st and st[-1] != '(': out.append(st.pop())
            st.pop()
        elif tok in PRECEDENCE:
            while st and st[-1] != '(' and PRECEDENCE[st[-1]] >= PRECEDENCE[tok]:
                out.append(st.pop())
            st.append(tok)
        else:
            out.append(tok)
        i += 1
    while st: out.append(st.pop())
    return out


def rpn_to_masm(tokens):
    asm = []
    for t in tokens:
        if t.lstrip('-').isdigit():
            asm.append(f"    push {t}")
        elif t.isidentifier():
            asm.append(f"    push DWORD PTR [{t}]")
        else:
            asm += ["    pop ebx", "    pop eax"]
            if t == '+':   asm += ["    add eax, ebx", "    push eax"]
            elif t == '-': asm += ["    sub eax, ebx", "    push eax"]
            elif t == '*': asm += ["    imul ebx", "    push eax"]
            elif t in ('/','%'):
                asm += ["    cdq", "    idiv ebx", "    push eax" if t=='/' else "    push edx"]
            else: raise ValueError(f"Неизвестный оператор {t}")
    return asm

# condition (cmp + jcc) helpers

JCC = {'<':'jl','<=':'jle','>':'jg','>=':'jge','==':'je','!=':'jne'}
NEG_JCC = {'<':'jge','<=':'jg','>':'jle','>=':'jl','==':'jne','!=':'je'}

label_counter = 0

def new_label(prefix='L'):
    global label_counter
    label = f"{prefix}{label_counter}"
    label_counter += 1
    return label

# main compile routine

def compile_source(src_text: str):
    asm_code, asm_data = [], []
    vars_declared, str_vars = set(), set()
    block_stack = []   # сохраняет {'type': 'if'|'while', ...}

    def ensure_var(v):
        if v not in vars_declared:
            vars_declared.add(v)
            asm_data.append(f"{v} dd ?")

    def add_string(literal):
        idx = len(str_vars)
        lbl = f"str{idx}"
        str_vars.add(lbl)
        segs = literal.split('\\n')
        bytes_ = []
        for i,s in enumerate(segs):
            if s: bytes_.append(f'"{s}"')
            if i < len(segs)-1: bytes_.append('0Dh,0Ah')
        bytes_.append('0')
        asm_data.append(f"{lbl} BYTE "+",".join(bytes_))
        return lbl

    # tokenised commands (split by ; and { )
    cmds = multi_split(src_text.replace('\n',' ').replace('\t',' '), [';','{'])

    for raw in cmds:
        parts = raw.strip().split()
        if not parts: continue
        head = parts[0]

        #  I/O 
        if head == 'input':
            var = parts[1].rstrip(',')
            if len(parts)==2:  # int
                ensure_var(var)
                asm_code += ["    call ReadInt", f"    mov [{var}], eax"]
            #   буфер для строк
                ln = int(parts[2].rstrip(','))
                if var not in vars_declared:
                    vars_declared.add(var); str_vars.add(var)
                    asm_data.append(f"{var} BYTE {ln} DUP(0)")
                asm_code += [f"    lea   edx, {var}", f"    mov   ecx, {ln}", "    call ReadString"]
            continue

        if head == 'print':
            rest = parts[1:]
            if rest[0].startswith('"'):
                lit = " ".join(rest)[1:-1].replace('""','"')
                lbl = add_string(lit)
                asm_code += [f"    lea   edx, {lbl}", "    call  WriteString"]
            elif len(rest)==1 and rest[0].rstrip(',') in str_vars:
                var = rest[0].rstrip(',')
                asm_code += [f"    lea   edx, {var}", "    call  WriteString"]
            else:
                rpn = infix_to_postfix(rest)
                asm_code += rpn_to_masm(rpn) + ["    pop eax", "    call  WriteInt"]
            continue

        #  IF 
        if head == 'if':
            cond_tokens = [t.rstrip(':') for t in parts[1:]]
            rpn = infix_to_postfix(cond_tokens)
            *arith, op = rpn
            asm_code += rpn_to_masm(arith)
            else_lbl = new_label('Else')
            end_lbl  = new_label('EndIf')
            asm_code += ["    pop ebx","    pop eax","    cmp eax, ebx", f"    {NEG_JCC[op]} {else_lbl}"]
            block_stack.append({'type':'if','else':else_lbl,'end':end_lbl})
            continue

        #  ELSE 
        if head.startswith('}else'):
            top = block_stack.pop()
            if top['type']!='if':
                raise SyntaxError('else без if')
            asm_code += [f"    jmp {top['end']}", f"{top['else']}:"]
            # помечаем, что мы теперь в ветке else
            block_stack.append({'type':'ifelse','end':top['end']})
            continue

        #  WHILE 
        if head == 'while':
            cond_tokens = [t.rstrip(':') for t in parts[1:]]
            rpn = infix_to_postfix(cond_tokens)
            *arith, op = rpn
            start_lbl = new_label('Loop')
            end_lbl   = new_label('EndLoop')
            asm_code.append(f"{start_lbl}:")
            asm_code += rpn_to_masm(arith)
            asm_code += ["    pop ebx","    pop eax","    cmp eax, ebx", f"    {NEG_JCC[op]} {end_lbl}"]
            block_stack.append({'type':'while','start':start_lbl,'end':end_lbl})
            continue

        #  BLOCK END 
        if head == '}':
            if not block_stack:
                continue  # лишняя скобка - игнорирование
            top = block_stack.pop()
            if top['type'].startswith('if'):
                asm_code.append(f"{top['end']}:")
            elif top['type']=='while':
                asm_code += [f"    jmp {top['start']}", f"{top['end']}:"]
            continue

        # присваивание / выражение
        if len(parts)>=3 and parts[1]=='=':
            target = parts[0]
            rpn = infix_to_postfix(parts[2:])
            asm_code += rpn_to_masm(rpn)
            ensure_var(target)
            asm_code += ["    pop eax", f"    mov [{target}], eax"]
            continue

    return asm_data, asm_code

# вход

def main():
    src = ask_source_path()
    with open(src,'r',encoding='utf-8') as f:
        txt = f.read()
    data, code = compile_source(txt)
    with open(out_path(src),'w',encoding='utf-8') as f:
        f.write('INCLUDE Irvine32.inc\n.data\n'+"\n".join(data)+"\n.code\nmain PROC\n"+"\n".join(code)+"\nexit\nmain ENDP\nEND main\n")
    print('Готово! Сгенерирован', out_path(src))

if __name__=='__main__':
    main()

"""Comment and string masking for static Lean source audits."""
def code_only(src):
    out=[]; i=0; block=0; string=False; line=False
    while i<len(src):
        if src[i]=='\n':
            line=False; out.append('\n'); i+=1; continue
        if line:
            out.append(' ');i+=1;continue
        if block:
            if src[i:i+2]=='/-': block+=1;out.extend('  ');i+=2;continue
            if src[i:i+2]=='-/': block-=1;out.extend('  ');i+=2;continue
            out.append(' ');i+=1;continue
        if string:
            if src[i]=='\\':out.extend('  ');i+=2;continue
            if src[i]=='"':string=False
            out.append(' ');i+=1;continue
        if src[i:i+2]=='/-':block=1;out.extend('  ');i+=2;continue
        if src[i:i+2]=='--':line=True;out.extend('  ');i+=2;continue
        if src[i]=='"':string=True;out.append(' ');i+=1;continue
        out.append(src[i]);i+=1
    if block or string:raise ValueError('unterminated Lean block comment or string')
    return ''.join(out)

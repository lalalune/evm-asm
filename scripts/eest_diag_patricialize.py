#!/usr/bin/env python3
"""Diagnostic: patricialize the source-fixture allocs (full state trie) to get
candidate roots for the precompile-withdrawal block, to identify what the ASM's
recomputed root corresponds to."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(__file__)))
import mpt_ref as m

EMPTY_CODE = m.k256(b"")

def nibs(b): 
    out=[]; 
    for x in b: out += [x>>4, x&0xf]
    return out

def common_prefix(keys):
    if not keys: return []
    cp=list(keys[0])
    for k in keys[1:]:
        i=0
        while i<len(cp) and i<len(k) and cp[i]==k[i]: i+=1
        cp=cp[:i]
    return cp

def build_trie(items):  # items: list of (nibbles, value_bytes); keys distinct
    if len(items)==1:
        k,v=items[0]; return m.leaf_node(k, v)
    cp=common_prefix([k for k,_ in items])
    if cp:
        child=build_trie([(k[len(cp):],v) for k,v in items])
        return m.extension_node(cp, m.node_ref(child))
    slots=[b"\x80"]*16; value=b""
    for nib in range(16):
        grp=[(k[1:],v) for k,v in items if k and k[0]==nib]
        if grp: slots[nib]=m.node_ref(build_trie(grp))
    emp=[v for k,v in items if not k]
    if emp: value=emp[0]
    return m.branch_node(slots, value)

def trie_root(items):
    if not items: return m.k256(m.rlp_bytes(b""))
    return m.k256(build_trie(items))

def storage_root(storage):
    items=[]
    for slot,val in storage.items():
        sk=int(slot,16).to_bytes(32,"big")
        v=int(val,16)
        items.append((nibs(m.k256(sk)), m.rlp_bytes(m.minimal_be(v))))
    return trie_root(items)

def patricialize(alloc):
    items=[]
    for addr,acct in alloc.items():
        a=int(addr,16).to_bytes(20,"big")
        nonce=int(acct.get("nonce","0x0"),16); bal=int(acct.get("balance","0x0"),16)
        code=bytes.fromhex(acct.get("code","0x")[2:])
        ch=m.k256(code) if code else EMPTY_CODE
        sr=storage_root(acct.get("storage") or {})
        val=m.account_encode(nonce, bal, sr, ch)
        items.append((nibs(m.k256(a)), val))
    return trie_root(items)

if __name__=="__main__":
    fp=sys.argv[1]; want=sys.argv[2]
    d=json.load(open(fp))
    for name,fx in d.items():
        if not isinstance(fx,dict) or want not in name: continue
        pre=fx["pre"]; post=fx["postState"]
        print("pre_root :", patricialize(pre).hex())
        print("post_root:", patricialize(post).hex(), "(== expected payload.state_root)")
        # post minus the NEW accounts (those absent in pre) = "insert(s) dropped"
        prek={k.lower() for k in pre}
        post_noins={k:v for k,v in post.items() if k.lower() in prek}
        print("post_minus_new:", patricialize(post_noins).hex(), "(system writes only, inserts dropped)")
        break

def build_struct(items):
    if len(items)==1: return ('leaf', items[0][0], items[0][1])
    cp=common_prefix([k for k,_ in items])
    if cp: return ('ext', cp, build_struct([(k[len(cp):],v) for k,v in items]))
    children={}; value=None
    for nib in range(16):
        grp=[(k[1:],v) for k,v in items if k and k[0]==nib]
        if grp: children[nib]=build_struct(grp)
    emp=[v for k,v in items if not k]
    if emp: value=emp[0]
    return ('branch', children, value)

def state_struct(alloc):
    items=[]
    for addr,acct in alloc.items():
        a=int(addr,16).to_bytes(20,"big")
        nonce=int(acct.get("nonce","0x0"),16); bal=int(acct.get("balance","0x0"),16)
        code=bytes.fromhex(acct.get("code","0x")[2:]); ch=m.k256(code) if code else EMPTY_CODE
        sr=storage_root(acct.get("storage") or {})
        items.append((nibs(m.k256(a)), m.account_encode(nonce,bal,sr,ch)))
    return build_struct(items)

def classify(node, path, depth=0):
    kind=node[0]
    if kind=='leaf':
        lk=node[1]
        # shared prefix
        sp=0
        while sp<len(lk) and sp<len(path) and lk[sp]==path[sp]: sp+=1
        if sp==len(lk) and sp==len(path): return f"depth{depth}: EXISTS (key present)"
        return f"depth{depth}: LEAF_SPLIT (leaf_keylen={len(lk)} remaining={len(path)} shared={sp})"
    if kind=='ext':
        ek=node[1]
        sp=0
        while sp<len(ek) and sp<len(path) and ek[sp]==path[sp]: sp+=1
        if sp==len(ek): return classify(node[2], path[len(ek):], depth+1)
        return f"depth{depth}: EXTENSION_SPLIT (extlen={len(ek)} matched={sp})"
    # branch
    children,value=node[1],node[2]
    if not path: return f"depth{depth}: BRANCH_VALUE (path ends at branch)"
    nib=path[0]
    if nib not in children: return f"depth{depth}: BRANCH_EMPTY_SLOT (nibble={nib})"
    return classify(children[nib], path[1:], depth+1)

def diag_path(fp, want, addr_hex):
    d=json.load(open(fp))
    for name,fx in d.items():
        if not isinstance(fx,dict) or want not in name: continue
        st=state_struct(fx["pre"])
        a=int(addr_hex,16).to_bytes(20,"big")
        path=nibs(m.k256(a))
        print(f"insert {addr_hex} -> path[:6]={path[:6]} :: {classify(st, path)}")
        return

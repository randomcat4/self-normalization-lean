from pathlib import Path
import hashlib, json, re, datetime
root=Path(r"C:/game/shao lean/drafts/oq56/unit251")
out=root/"author-01"
source=out/"OriginalLevelDependentClippedSourcePackage.lean"
raw=source.read_bytes()
s=raw.decode("utf-8")
lines=s.splitlines(keepends=True)
def binding(p):
    b=p.read_bytes()
    return {"path":str(p).replace("\\","/"),"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()}
preamble=(root/"freeze-01/FROZEN-PREAMBLE.txt").read_bytes()
head=(root/"freeze-01/FROZEN-HEAD.txt").read_bytes()
closing=(root/"freeze-01/FROZEN-CLOSING.txt").read_bytes()
body=(out/"PROOF-BODY.txt").read_bytes()
decls=[]
for i,line in enumerate(lines):
    m=re.match(r"^( *)(let|have)\s+([^\s(:]+)",line)
    if not m: continue
    indent=len(m[1]); end=i+1
    while end<len(lines):
        if lines[end].strip() and len(lines[end])-len(lines[end].lstrip(" ")) <= indent:
            break
        end+=1
    text="".join(lines[i:end]).rstrip("\n")
    if ":=" not in text:
        raise ValueError("Missing RHS at line "+str(i+1))
    header,rhs=text.split(":=",1)
    kind="frozen-conclusion-let" if m[2]=="let" and i<s[:s.index(" := by")].count("\n") else "proof-local-"+m[2]
    decls.append({"index":len(decls)+1,"name":m[3],"kind":kind,"lineStart":i+1,"lineEnd":end,
       "indent":indent,"declarationHeader":header.strip(),"fullRHS":rhs.strip(),
       "exactDeclaration":text,"explicitTypeInHeader":":" in header,
       "scope":{"container":"main theorem","endLine":len(lines)-3}})
for d in decls:
    containers=[p for p in decls if p["lineStart"]<d["lineStart"]<=d["lineEnd"]<=p["lineEnd"]]
    if containers:
        p=max(containers,key=lambda x:x["lineStart"])
        d["scope"]={"container":p["name"],"endLine":p["lineEnd"]}
theorems=[(i+1,l.strip()) for i,l in enumerate(lines) if re.match(r"^theorem\s",l)]
forbidden={t:[i+1 for i,l in enumerate(lines) if re.search(r"\b"+t+r"\b",l)] for t in ["sorry","admit","axiom","unsafe","native_decide"]}
forbidden={k:v for k,v in forbidden.items() if v}
checks={
 "schema":"oq56-unit251-source-static-check-v1","atUTC":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "source":binding(source),"UTF8Decode":True,"BOM":raw.startswith(b"\xef\xbb\xbf"),
 "CRbytes":raw.count(b"\r"),"LF":raw.count(b"\n"),
 "singleFinalNewline":raw.endswith(b"\n") and not raw.endswith(b"\n\n"),
 "exactPreamble":raw.startswith(preamble),"exactFrozenHead":raw[len(preamble):len(preamble)+len(head)]==head,
 "exactClosing":raw.endswith(closing),"exactComposition":raw==preamble+head+body+closing,
 "publicTheorems":theorems,"forbiddenTokens":forbidden,
 "topLevelOtherDeclarations":[(i+1,l.strip()) for i,l in enumerate(lines) if re.match(r"^(?:private\s+)?(?:def|abbrev|instance|opaque|axiom|lemma)\s",l)],
 "allLocalDeclarationHeadersTyped":all(d["explicitTypeInHeader"] for d in decls),
 "sourceInventoryCount":len(decls),"sourceInventoryKindCounts":{k:sum(d["kind"]==k for d in decls) for k in sorted(set(d["kind"] for d in decls))},
 "sourceInventoryIsMachineOwnerCount":False,"LeanRun":False,"serverRun":False,"independentReview":False,"qualified":False
}
checks["PASS"]=all([checks["UTF8Decode"],not checks["BOM"],checks["CRbytes"]==0,checks["singleFinalNewline"],checks["exactPreamble"],checks["exactFrozenHead"],checks["exactClosing"],checks["exactComposition"],len(theorems)==1,not forbidden,not checks["topLevelOtherDeclarations"],checks["allLocalDeclarationHeadersTyped"]])
inventory={"schema":"oq56-unit251-source-local-declaration-inventory-v1","source":binding(source),"inventoryNotElaborated":True,
"warning":"These are exact source let/have declarations and lexical scopes, never actual machine owners, TYPE or VALUE evidence.",
"declarations":decls}
(out/"SOURCE-INVENTORY.json").write_text(json.dumps(inventory,ensure_ascii=False,indent=2)+"\n",encoding="utf-8",newline="\n")
md=["# Unit251 complete source-local declarations","", "Source-only inventory. This is not machine owner/TYPE/VALUE evidence.",""]
for d in decls:
    md += [f"## {d['index']}. {d['name']} ({d['kind']}, lines {d['lineStart']}-{d['lineEnd']})",
       "",f"Lexical container: {d['scope']['container']}; scope ends at line {d['scope']['endLine']}.",
       "","Full explicit header, parameter binders and RHS:","","```lean",d["exactDeclaration"],"```",""]
(out/"SOURCE-INVENTORY.md").write_text("\n".join(md)+"\n",encoding="utf-8",newline="\n")
(out/"STATIC-CHECK.json").write_text(json.dumps(checks,ensure_ascii=False,indent=2)+"\n",encoding="utf-8",newline="\n")
print(json.dumps({k:v for k,v in checks.items() if k not in ["publicTheorems"]},ensure_ascii=False,indent=2))

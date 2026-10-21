# Required format repair and exact-source certification

The actual staged `git diff --check` rejected CRLF/EOF whitespace in the new Laplace source and three author-document copies. The source author applied only `replace(CRLF, LF).rstrip(LF) + LF`: 5 CRLF sequences and four trailing empty lines were removed, changing 15121 bytes to 15112 bytes. No code token or proof changed. The previous source remains archived on the server.

| LaplaceTail source | SHA256 |
|---|---|
| Original reviewed source | 5ceb63a9c3955f8479b6c0def43e9c2fdeb9ac2f915aa23553cb2243c3f8ffb9 |
| Current source | 664df6aa0c3221b9a0212580a20b141b7f0a0eea1d8adbeb4af15d486dcf68e2 |

The author repeated the actual target, uniquely regenerated the olean, and audited all 29 module-owned constants. The independent reviewer verified the exact byte transform, repeated the no-o target and complete-source audit, and appended a superseding current-source section to the unchanged original formal review. The original mathematics ticket and anonymous proof snapshot remain preserved. The lead repeats only the affected import and combined audits, with the current source hash in the final receipts.

Updated author receipt/declaration copies use UTF-8/LF. The submitted anonymous proof copy has only the same line-ending/EOF normalization: original snapshot SHA256 `a367fe447ae78287d4474f8b10f6c3141be22f34865606e940eb74d4ee76d62e`, normalized copy SHA256 `5455a8f2cd1b700df5e75e33d7f1b3c39ba85aa38d2c31fd11cb6d47ccef5207`. The original snapshot remains the one identified by the mathematics review; its server archive is `repro_outputs/oq4-survival-inputs-format/oq4-laplace-proof.md.before`.

The original frozen statement is unchanged. All complete roots remain OPEN.

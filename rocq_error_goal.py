#!/usr/bin/env python3
import re
import sys
import subprocess
from pathlib import Path
from dataclasses import dataclass


ERROR_RE = re.compile(
    r'File\s+"(?P<file>.+?)",\s+line\s+(?P<line>\d+),\s+characters\s+(?P<c1>\d+)-(?P<c2>\d+):'
)

PROOF_START_RE = re.compile(r'^\s*Proof\s*\.\s*$')
PROOF_END_RE = re.compile(r'^\s*(Qed|Defined|Admitted|Abort)\s*\.\s*$')


@dataclass
class Sentence:
    text: str
    start_line: int
    end_line: int


def run(cmd, *, input_text=None):
    return subprocess.run(
        cmd,
        input=input_text,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def run_compile(path: str, extra_args: list[str]):
    return run(["rocq", "compile", *extra_args, path])


def parse_error(stderr: str):
    m = ERROR_RE.search(stderr)
    if not m:
        return None
    return {
        "file": m.group("file"),
        "line": int(m.group("line")),
        "char_start": int(m.group("c1")),
        "char_end": int(m.group("c2")),
    }


def strip_comments_preserve_layout(text: str) -> str:
    """
    Rocq の (* ... *) コメントを雑に除去する。
    文字数と改行数をなるべく保つため、コメント部分は空白に置換する。
    ネストコメントにも対応する簡易版。
    文字列リテラル等の厳密処理はしない。
    """
    out = []
    i = 0
    n = len(text)
    depth = 0

    while i < n:
        if i + 1 < n and text[i] == "(" and text[i + 1] == "*":
            depth += 1
            out.append(" ")
            out.append(" ")
            i += 2
            continue

        if depth > 0:
            if i + 1 < n and text[i] == "*" and text[i + 1] == ")":
                depth -= 1
                out.append(" ")
                out.append(" ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            continue

        out.append(text[i])
        i += 1

    return "".join(out)


def split_sentences(text: str) -> list[Sentence]:
    """
    Rocq を完全には解析しない簡易 sentence splitter。
    '.' 単位で文を切るが、コメントは事前に除去する。
    文字列等は厳密には扱わない。
    """
    clean = strip_comments_preserve_layout(text)

    sentences = []
    buf = []
    start_line = 1
    line = 1

    i = 0
    n = len(clean)
    while i < n:
        ch = clean[i]
        buf.append(text[i])  # 元の文字を保持
        if ch == ".":
            sent_text = "".join(buf)
            end_line = line
            sentences.append(Sentence(sent_text, start_line, end_line))
            buf = []
            start_line = line
        if ch == "\n":
            line += 1
            if not buf:
                start_line = line
        i += 1

    # 末尾に '.' のない残り
    if buf:
        sentences.append(Sentence("".join(buf), start_line, line))

    return sentences


def find_latest_proof_block_before_line(sentences: list[Sentence], error_line: int):
    """
    error_line より前で始まった最後の Proof. ブロックを見つける。
    戻り値:
      (prefix_sentences, proof_sentences)
    ここで proof_sentences は Proof. から error_line直前までの文列。
    """
    idx_before_error = None
    for i, s in enumerate(sentences):
        if s.start_line <= error_line:
            idx_before_error = i
        else:
            break

    if idx_before_error is None:
        return None, None

    last_proof_start = None
    for i in range(idx_before_error, -1, -1):
        txt = s_strip(sentences[i].text)
        if PROOF_START_RE.match(txt):
            last_proof_start = i
            break
        if PROOF_END_RE.match(txt):
            # 直前に proof 終端が見つかったなら、エラーは proof 外の可能性が高い
            return None, None

    if last_proof_start is None:
        return None, None

    prefix = sentences[:last_proof_start]
    proof = []
    for i in range(last_proof_start, idx_before_error + 1):
        txt = sentences[i].text
        proof.append(sentences[i])
        if PROOF_END_RE.match(s_strip(txt)):
            break

    return prefix, proof


def s_strip(s: str) -> str:
    return s.strip()


def try_repl(prefix_sentences: list[Sentence], proof_sentences: list[Sentence], extra_args: list[str]):
    """
    proof_sentences を 1文ずつ流し、失敗したら直前で止める。
    戻り値:
      {
        ok_prefix_count: int,
        failed_sentence_index: int | None,
        failed_sentence: Sentence | None,
        repl_stdout: str,
        repl_stderr: str,
      }
    """
    base = "".join(s.text for s in prefix_sentences)
    accepted = []

    # まず prefix + accepted + Show. を毎回流す
    for i, sent in enumerate(proof_sentences):
        candidate = base + "".join(s.text for s in accepted) + sent.text
        proc = run(["rocq", "repl", "-quiet", *extra_args], input_text=candidate)
        if proc.returncode != 0:
            # この文は失敗
            show_proc = run(
                ["rocq", "repl", "-quiet", *extra_args],
                input_text=base + "".join(s.text for s in accepted) + "\nShow.\n",
            )
            return {
                "ok_prefix_count": len(accepted),
                "failed_sentence_index": i,
                "failed_sentence": sent,
                "repl_stdout": show_proc.stdout,
                "repl_stderr": show_proc.stderr,
            }
        accepted.append(sent)

    # 全文通った
    show_proc = run(
        ["rocq", "repl", "-quiet", *extra_args],
        input_text=base + "".join(s.text for s in accepted) + "\nShow.\n",
    )
    return {
        "ok_prefix_count": len(accepted),
        "failed_sentence_index": None,
        "failed_sentence": None,
        "repl_stdout": show_proc.stdout,
        "repl_stderr": show_proc.stderr,
    }


def extract_rocq_args(argv: list[str]):
    """
    使い方:
      script.py [rocq args ...] target.v
    最後の .v を対象ファイルとみなす。
    """
    if len(argv) < 2:
        print(f"usage: {argv[0]} [rocq-args ...] target.v", file=sys.stderr)
        sys.exit(2)

    v_files = [a for a in argv[1:] if a.endswith(".v")]
    if not v_files:
        print("No .v file given.", file=sys.stderr)
        sys.exit(2)

    target = v_files[-1]
    args = argv[1:]
    args.remove(target)
    return args, target


def print_sentence_summary(title: str, sent: Sentence | None):
    print(title)
    if sent is None:
        print("  (none)")
        return
    first = sent.text.strip().splitlines()
    preview = first[0] if first else ""
    if len(preview) > 120:
        preview = preview[:120] + "..."
    print(f"  lines: {sent.start_line}-{sent.end_line}")
    print(f"  text : {preview}")


def main():
    extra_args, path = extract_rocq_args(sys.argv)

    compile_proc = run_compile(path, extra_args)

    if compile_proc.returncode == 0:
        print("No compile error found.")
        if compile_proc.stdout:
            print(compile_proc.stdout, end="")
        sys.exit(0)

    info = parse_error(compile_proc.stderr)
    if not info:
        print("Compilation failed, but could not parse error location.")
        print("---- stdout ----")
        print(compile_proc.stdout, end="")
        print("---- stderr ----")
        print(compile_proc.stderr, end="")
        sys.exit(1)

    print("Compile error found:")
    print(f'  file : {info["file"]}')
    print(f'  line : {info["line"]}')
    print(f'  chars: {info["char_start"]}-{info["char_end"]}')
    print()

    text = Path(path).read_text(encoding="utf-8")
    sentences = split_sentences(text)
    prefix, proof = find_latest_proof_block_before_line(sentences, info["line"])

    print("Original compiler message:")
    print(compile_proc.stderr, end="")
    print()

    if prefix is None or proof is None:
        print("Could not find an active proof block before the error line.")
        print("This likely means the error is outside proof mode, or the simple parser got confused.")
        sys.exit(1)

    result = try_repl(prefix, proof, extra_args)

    if result["failed_sentence_index"] is None:
        print("All sentences in the detected proof prefix were accepted by rocq repl.")
        print("The compile error may be after that point, or caused by context outside this simplified replay.")
    else:
        print(f"Replay stopped at proof sentence index: {result['failed_sentence_index']}")
        print_sentence_summary("Failed sentence:", result["failed_sentence"])
        prev = proof[result["failed_sentence_index"] - 1] if result["failed_sentence_index"] > 0 else None
        print_sentence_summary("Previous accepted sentence:", prev)
        print()

    print("Goal just before the failing sentence:")
    if result["repl_stdout"].strip():
        print("---- repl stdout ----")
        print(result["repl_stdout"], end="")
        print("---------------------")


if __name__ == "__main__":
    main()
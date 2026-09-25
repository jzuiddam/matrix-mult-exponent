# Frozen statements

Each file here holds one statement, `def S_<id> : Prop := …`, used by the proof. The statements
were written and frozen in the development repository before they were proved, and were never edited
afterwards. The files here are copies of those frozen statements. Their statement text is
byte-identical, and its SHA-256 is the value given in each file's header and in the tables below.
Only the header comment was rewritten for publication. It has the same number of lines as before, so
every declaration is on the same line.

Two files keep development-time wording inside their hashed statement text, which cannot change without changing the hash: the docstring of `S_T8_1` and a marker comment in `V17_D_Inventory.1`. Those words, the `V17_` prefix of the ids, and the Lean namespace prefix `P2M.V17_` name the development repository's registry of frozen statements and its plan version; they carry no mathematical content.

**The header.** Every file starts with a block comment of eight lines:

- `id`: the statement's identifier in the development repository. The number after the dot tells
  apart statements registered under the same name; a statement that turned out to be wrong was not
  edited but replaced by one with a new number, so some numbers are absent here.
- `paper_clause`: the part of the paper the statement formalises. `P/<file>.tex:<lines>` refers to
  the paper's LaTeX source (arXiv:2404.16349), as in the docstrings of the modules.
- `sha256`: the SHA-256 of the statement text, which is every byte after the header's closing line
  `-/`.

To recompute the hash of a statement file, run, from the root of this tree:

```
sed '1,/^-\/$/d' PLATFORM/Statements/T8.1.lean | sha256sum
```

The `sed` command deletes the lines up to and including the first line that is exactly `-/`, that is,
the header.

**The two statements of the result:**

| id | definition | proved by | file SHA-256 | statement SHA-256 |
|---|---|---|---|---|
| T8.1 | `S_T8_1` | `OmegaBound.omegaMM_lt_2371339` | `3cb1823233095001bd85820d5434c6dc7d1595d14679c8ba6b7567e495ad6e0a` | `9f5ec0e45a9b074b54392cb879da97608f72b6d234da4513a118ed7714e99182` |
| T8_F.1 | `OmegaBound.ADVXXZGeneral.S_T8_F_1` | `OmegaBound.omegaMM_lt_2371339_allFields` | `7209a3d1fc0a059215bfad9716f0af0c007111185c4fbff034970d9de5cba9f3` | `326ade3088dcc81fe000c559b6a1276e70865e5451bc8fd6b5ba8005ba033f40` |

`release/CheckAxioms.lean` elaborates `example : S_T8_1 := OmegaBound.omegaMM_lt_2371339` and
`example : OmegaBound.ADVXXZGeneral.S_T8_F_1.{u} := OmegaBound.omegaMM_lt_2371339_allFields.{u}`.

**The other 15 files** are statements of intermediate theorems. Modules of the proof import
them; they are shipped only so that the tree builds:

| file | statement SHA-256 |
|---|---|
| `PLATFORM/Statements/V17_C_Exact.3.lean` | `3074a29abca3f39389737b615cf10b5f098b185e91311438388a9eabcbc1ff55` |
| `PLATFORM/Statements/V17_C_Exact.4.lean` | `1954fdca8a6f004d5c8e6c21d4c92d847837853db607c027560d888c8044c81a` |
| `PLATFORM/Statements/V17_D_Inventory.1.lean` | `9b63c4e64dce8ac8ca0bcd1f87652fab59b9a7c2ef60f0b1c5101e9aa02bf270` |
| `PLATFORM/Statements/V17_G_Exact.1.lean` | `4f8bfd74f1bd4690eb07b165b6ac486dc6afddcffb6c6b80273f830fb2b5a971` |
| `PLATFORM/Statements/V17_G_Exact.2.lean` | `b7766a9fd572930a64523d264aade5fcf10568369cfa962b19bda4a1c179439e` |
| `PLATFORM/Statements/V17_G_Near.1.lean` | `12cd5eaa3dafd2dd2f7a967aa52fc9186b2ee2c7824fdd567c72566910f5bde5` |
| `PLATFORM/Statements/V17_I_Apply.1.lean` | `7b87bfb76d785fa94df2cf025d8e94a6d035edfde9ba5f57e5ee30153d09cbf3` |
| `PLATFORM/Statements/V17_I_Apply.2.lean` | `cf55e16c95635c41fc87343f1f73cdf1896f732d4ee857ca44afc0e10337149c` |
| `PLATFORM/Statements/V17_I_Apply.3.lean` | `4952e50bd00127999e13a645c02fda623fdd67d7b2c4474c50ab2b86b90c3e8e` |
| `PLATFORM/Statements/V17_I_Apply.4.lean` | `c1d97c2f54a79383534fe542813da3b44b689850e83c5f1fb0692b9690d68acf` |
| `PLATFORM/Statements/V17_I_Rows.10.lean` | `1c23401d8ecd8179ba6995fcaac70f65f4a9317f1e8f52a5f8f4ad17f052c04a` |
| `PLATFORM/Statements/V17_I_Rows.8.lean` | `bd2ed168a92db28b6f433504f0daf0217b19f7ad8782102f440834af03efd1ec` |
| `PLATFORM/Statements/V17_N_Closure.1.lean` | `7d431e2ba16f9d0d374e860efc9c284b80f678729605a5e48abae333fb59d8a3` |
| `PLATFORM/Statements/V17_N_Closure.2.lean` | `2b86a662246b1ec42a2f8d2cf646c19c1071320731cc6f3be65cff88ab751942` |
| `PLATFORM/Statements/V17_N_Iterate.1.lean` | `a084d1d5300bdd1e7142bb5245223c1eb878661a96eec88bd69cbc66ad52ba9f` |

module

public import ConLeche.Kernel.Name
public import ConLeche.Kernel.TrustAxioms
/- The `#guard`s below are EVALUATED, so the constants they name have to be
reachable from meta code too; a plain import is not.  A module needed at
both levels is imported twice. -/
meta import ConLeche.Kernel.Name
meta import ConLeche.Kernel.TrustAxioms

public section

/-!
# Display rendering of input names and strings (task #365)

Every name and every raw string the checker prints comes from the input
stream, so the rendering (`Name.render`, `Display.str`,
`ConLeche/Kernel/Name.lean`) must not let one reach the terminal or a CI
log as a control sequence, an invisible character or a spoofed name.
These guards pin the format: identifier-shaped components bare, every
other component `«…»` with `\` doubled and the unsafe characters (and
`»`) as `\u{XXXX}`, numeric components as decimals, and the cap.
-/

namespace ConLecheTests.Display

open ConLeche

/-- A name from its string components, root first. -/
def mk (cs : List String) : Name := cs.foldl .str .anonymous

/-- The rendering contains no character the display must escape, and
no newline, so no line of a message can start with `::`. -/
def clean (s : String) : Bool := !s.any Display.unsafeChar

-- Ordinary names, including the Unicode Lean names use, print as Lean does.
#guard toString (mk ["Nat", "add_comm"]) == "Nat.add_comm"
#guard toString (mk ["α₁", "ℕ", "x'", "h?", "ok!"]) == "α₁.ℕ.x'.h?.ok!"
#guard toString (mk ["_private"]) == "_private"

-- The anonymous name, and a component that spells it.
#guard toString Name.anonymous == "[anonymous]"
#guard toString (mk ["[anonymous]"]) == "«[anonymous]»"

-- A numeric component is a bare decimal; a string component that looks
-- like one is quoted, so the two never print alike.
#guard toString (Name.num (mk ["x"]) 3) == "x.3"
#guard toString (mk ["x", "3"]) == "x.«3»"
#guard toString (Name.num .anonymous 7) == "7"

-- A `.` inside a component is not a separator.
#guard toString (mk ["a.b"]) == "«a.b»"
#guard toString (mk ["a", "b"]) == "a.b"

-- `«` stays, `»` is escaped (Lean itself gives up escaping there), and a
-- backslash is doubled so an escape in the input is not one in the output.
#guard toString (mk ["«x»"]) == "««x\\u{00BB}»"
#guard toString (mk ["a\\u{001B}"]) == "«a\\\\u{001B}»"
#guard toString (mk [""]) == "«»"

-- Control characters: ESC, newline, carriage return, DEL, a C1 control.
#guard toString (mk ["a\x1b[31mb"]) == "«a\\u{001B}[31mb»"
#guard toString (mk ["c\nd\re"]) == "«c\\u{000A}d\\u{000D}e»"
#guard toString (mk ["\x7f\u0085"]) == "«\\u{007F}\\u{0085}»"

-- Bidi controls, zero-width and other invisible characters, odd spaces.
#guard toString (mk ["admin‮txt.exe"]) == "«admin\\u{202E}txt.exe»"
#guard toString (mk ["a​b"]) == "«a\\u{200B}b»"
#guard toString (mk ["⁦⁩‎‏؜"]) ==
  "«\\u{2066}\\u{2069}\\u{200E}\\u{200F}\\u{061C}»"
#guard toString (mk ["﻿⁠‍"]) == "«\\u{FEFF}\\u{2060}\\u{200D}»"
#guard toString (mk ["a b"]) == "«a\\u{00A0}b»"
#guard toString (mk ["tag".push (Char.ofNat 0xE0041)]) == "«tag\\u{E0041}»"
#guard toString (mk ["a b"]) == "«a b»"

-- A GitHub Actions workflow command after a newline stays on the line.
#guard toString (mk ["ok\n::error::pwned"]) == "«ok\\u{000A}::error::pwned»"
#guard clean (toString (mk ["ok\n::error::pwned", "\x1b]0;t\x07"]))

-- The cap: 512 characters, then the elision marker with the count of the
-- name's characters not shown.
#guard toString (mk [String.ofList (List.replicate 600 'x')]) ==
  String.ofList (List.replicate 512 'x') ++ "…[88 more characters]"
#guard (toString (mk [String.ofList (List.replicate 600 '\x1b')])).length ≤ 512 + 30
#guard (toString (mk (List.replicate 1000 "ab"))).endsWith "…[2487 more characters]"

-- Raw strings from the input (a `safety` field, a quotient kind).
#guard Display.str "unsafe" == "\"unsafe\""
#guard Display.str "a\x1b[1;32m\n\"b\"\\" == "\"a\\u{001B}[1;32m\\u{000A}\\u{0022}b\\u{0022}\\\\\""
#guard clean (Display.str "\x1b[2K\rcon-leche: accepted\n::error::x")

-- The `_native` tactic component is input too.
#guard nonStdAxiomMsg (mk ["f", "_native", "evil\n::error::x", "ax_1"]) ==
  "non-standard axiom (f._native.«evil\\u{000A}::error::x».ax_1), apparently added by the \
    `«evil\\u{000A}::error::x»` tactic; con-leche does not support such axioms at the moment"

end ConLecheTests.Display

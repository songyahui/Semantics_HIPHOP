let no_color =
  match Sys.getenv_opt "SLEEK_COLOR" with
  | None       -> false
  | Some "off" -> true
  | Some _     -> false


let color_string s = if no_color then "" else s

let reset = color_string "\027[0m"

let bold = color_string "\027[1m"

let no_bold = color_string "\027[22m"

let underline = color_string "\027[4m"

let no_underline = color_string "\027[24m"

let overline = color_string "\027[53m"

let no_overline = color_string "\027[55m"

let italic = color_string "\027[3m"

let no_italic = color_string "\027[23m"

let red = color_string "\027[31m"

let green = color_string "\027[32m"

let yellow = color_string "\027[33m"

let blue = color_string "\027[34m"

let magenta = color_string "\027[35m"

let cyan = color_string "\027[36m"

let white = color_string "\027[37m"

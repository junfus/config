-- noval_formatter.lua
--
-- Reads a UTF-8 text file and rewrites it so that:
-- - Each paragraph becomes a single output line
-- - Paragraph separation is normalized (no blank lines between paragraphs; chapter
--   title spacing is added later)
-- - Whitespace is normalized for mixed Chinese/English text
--
-- Paragraph boundary rules:
-- - Blank/whitespace-only lines split paragraphs
-- - A line that *starts with indentation* also starts a new paragraph
--   (useful for mixed formats where paragraphs are indicated by leading spaces)
--
-- Pipeline (in main):
--   1) join_paragraphs
--   2) format_chapter_titles
--   3) replace_corner_quotes
--   4) normalize_quote_levels_in_ok_chapters
--   5) move_trailing_open_quote_to_next_line
--   6) write output
--   7) validate quotes chapter-by-chapter and write log
--

-- === Paragraph punctuation character definitions ===
-- ASCII punctuation
local PUNCT_ASCII_EXCLAIM = 0x21              -- !
local PUNCT_ASCII_PAREN_OPEN = 0x28           -- (
local PUNCT_ASCII_PAREN_CLOSE = 0x29          -- )
local PUNCT_ASCII_COMMA = 0x2C                -- ,
local PUNCT_ASCII_PERIOD = 0x2E               -- .
local PUNCT_ASCII_COLON = 0x3A                -- :
local PUNCT_ASCII_SEMICOLON = 0x3B            -- ;
local PUNCT_ASCII_QUESTION = 0x3F             -- ?
local PUNCT_ASCII_TILDE = 0x7E                -- ~
-- Unicode punctuation and quotes
local PUNCT_EM_DASH = 0x2014                  -- —
local PUNCT_ELLIPSIS = 0x2026                 -- …
local PUNCT_END_PERIOD = 0x3002               -- 。
local PUNCT_BRACKET_CLOSE_CN = 0x3011         -- 】
local PUNCT_DOUBLE_ANGLE_QUOTE_CLOSE = 0x300B -- 》
local PUNCT_QUOTE_OPEN = 0x300C               -- 「
local PUNCT_QUOTE_CLOSE = 0x300D              -- 」
local PUNCT_QUOTE_OPEN_NESTED = 0x300E        -- 『
local PUNCT_QUOTE_CLOSE_NESTED = 0x300F       -- 』
local PUNCT_PAREN_OPEN_CN = 0xFF08            -- （
local PUNCT_PAREN_CLOSE_CN = 0xFF09           -- ）
local PUNCT_END_EXCLAIM = 0xFF01              -- ！
local PUNCT_COMMA_CN = 0xFF0C                 -- ，
local PUNCT_COLON_CN = 0xFF1A                 -- ：
local PUNCT_SEMICOLON_CN = 0xFF1B             -- ；
local PUNCT_END_QUESTION = 0xFF1F             -- ？
local PUNCT_TILDE_CN = 0xFF5E                 -- ～

-- === IO / basic utilities ===

local function die(message)
    io.stderr:write(message .. "\n")
    os.exit(2)
end

local function read_all(path)
    local file = assert(io.open(path, "rb"))
    local content = file:read("*a")
    file:close()

    return content
end

local function write_all(path, content)
    local file = assert(io.open(path, "wb"))
    file:write(content)
    file:close()
end

local function file_exists(path)
    local file = io.open(path, "rb")
    if file ~= nil then
        file:close()

        return true
    end

    return false
end

local function delete_file_if_exists(path)
    pcall(os.remove, path)
end

local function strip_utf8_bom(text)
    -- UTF-8 BOM bytes: EF BB BF
    if text:sub(1, 3) == "\239\187\191" then
        return text:sub(4)
    end

    return text
end

local function normalize_newlines(text)
    text = text:gsub("\r\n", "\n")
    text = text:gsub("\r", "\n")

    return text
end

local function trim_ends(line)
    -- ASCII whitespace trim (spaces/tabs/etc.).
    line = line:gsub("^%s+", "")
    line = line:gsub("%s+$", "")
    -- Full-width space trim.
    line = line:gsub("^　+", "")
    line = line:gsub("　+$", "")

    return line
end

local function consume_indent_prefix(line, start_pos)
    -- Consume leading indentation (spaces, tabs, full-width spaces) from s starting at start_pos.
    local i = start_pos
    while i <= #line do
        local b = line:byte(i)
        if b == 0x20 or b == 0x09 then
            i = i + 1
        elseif b == 0xE3 and line:byte(i + 1) == 0x80 and line:byte(i + 2) == 0x80 then
            i = i + 3
        else
            break
        end
    end

    return i
end

-- === Text normalization helpers ===

local function is_ascii_word_cp(cp)
    return (cp >= 0x30 and cp <= 0x39) -- 0-9
        or (cp >= 0x41 and cp <= 0x5A) -- A-Z
        or (cp >= 0x61 and cp <= 0x7A) -- a-z
        or (cp == 0x5F)                -- _
end

local function normalize_whitespace_preserve_english(line)
    -- Keep whitespace *only* when it is between ASCII word characters (English words).
    -- Remove whitespace around Chinese chars/punctuation/symbols.
    -- Whitespace considered: space, tab, full-width space.
    local chars = {}
    for _, cp in utf8.codes(line) do
        chars[#chars + 1] = cp
    end

    local function is_ws(cp)
        return cp == 0x20 or cp == 0x09 or cp == 0x3000
    end

    local function prev_non_ws(i)
        for j = i - 1, 1, -1 do
            if not is_ws(chars[j]) then
                return chars[j]
            end
        end

        return nil
    end

    local function next_non_ws(i)
        for j = i + 1, #chars do
            if not is_ws(chars[j]) then
                return chars[j]
            end
        end

        return nil
    end

    local out = {}
    for i, cp in ipairs(chars) do
        if is_ws(cp) then
            local left = prev_non_ws(i)
            local right = next_non_ws(i)
            if left ~= nil and right ~= nil and is_ascii_word_cp(left) and is_ascii_word_cp(right) then
                -- Collapse any run of whitespace between English word chars to a single ASCII space.
                if out[#out] ~= " " then
                    out[#out + 1] = " "
                end
            end
        else
            out[#out + 1] = utf8.char(cp)
        end
    end

    return table.concat(out)
end

local function ends_with_ascii_word(text)
    return text:match("[A-Za-z0-9_]$") ~= nil
end

local function starts_with_ascii_word(text)
    return text:match("^[A-Za-z0-9_]") ~= nil
end

local PUNCT_PAIRS = {
    [PUNCT_ASCII_COMMA] = { ascii = PUNCT_ASCII_COMMA, full = PUNCT_COMMA_CN },
    [PUNCT_ASCII_PERIOD] = { ascii = PUNCT_ASCII_PERIOD, full = PUNCT_END_PERIOD },
    [PUNCT_ASCII_PAREN_OPEN] = { ascii = PUNCT_ASCII_PAREN_OPEN, full = PUNCT_PAREN_OPEN_CN },
    [PUNCT_ASCII_PAREN_CLOSE] = { ascii = PUNCT_ASCII_PAREN_CLOSE, full = PUNCT_PAREN_CLOSE_CN },
    [PUNCT_ASCII_EXCLAIM] = { ascii = PUNCT_ASCII_EXCLAIM, full = PUNCT_END_EXCLAIM },
    [PUNCT_ASCII_QUESTION] = { ascii = PUNCT_ASCII_QUESTION, full = PUNCT_END_QUESTION },
    [PUNCT_ASCII_COLON] = { ascii = PUNCT_ASCII_COLON, full = PUNCT_COLON_CN },
    [PUNCT_ASCII_SEMICOLON] = { ascii = PUNCT_ASCII_SEMICOLON, full = PUNCT_SEMICOLON_CN },
    [PUNCT_ASCII_TILDE] = { ascii = PUNCT_ASCII_TILDE, full = PUNCT_TILDE_CN },
    [PUNCT_COMMA_CN] = { ascii = PUNCT_ASCII_COMMA, full = PUNCT_COMMA_CN },
    [PUNCT_END_PERIOD] = { ascii = PUNCT_ASCII_PERIOD, full = PUNCT_END_PERIOD },
    [PUNCT_PAREN_OPEN_CN] = { ascii = PUNCT_ASCII_PAREN_OPEN, full = PUNCT_PAREN_OPEN_CN },
    [PUNCT_PAREN_CLOSE_CN] = { ascii = PUNCT_ASCII_PAREN_CLOSE, full = PUNCT_PAREN_CLOSE_CN },
    [PUNCT_END_EXCLAIM] = { ascii = PUNCT_ASCII_EXCLAIM, full = PUNCT_END_EXCLAIM },
    [PUNCT_END_QUESTION] = { ascii = PUNCT_ASCII_QUESTION, full = PUNCT_END_QUESTION },
    [PUNCT_COLON_CN] = { ascii = PUNCT_ASCII_COLON, full = PUNCT_COLON_CN },
    [PUNCT_SEMICOLON_CN] = { ascii = PUNCT_ASCII_SEMICOLON, full = PUNCT_SEMICOLON_CN },
    [PUNCT_TILDE_CN] = { ascii = PUNCT_ASCII_TILDE, full = PUNCT_TILDE_CN },
}

local function normalize_punctuation(line)
    -- Normalize punctuation for mixed Chinese/English text.
    -- Rule: for , ! ? : ; choose ASCII if the punctuation follows an ASCII “word”
    -- character (A-Z, a-z, 0-9, _), otherwise choose the Chinese full-width form.
    -- This works both ways, meaning it can also fix wrongly-used Chinese punctuation
    -- inside English/number contexts.

    local out = {}
    local prev_non_ws_is_word = false
    for _, cp in utf8.codes(line) do
        if cp == 0x20 or cp == 0x09 then
            out[#out + 1] = utf8.char(cp)
        else
            local p = PUNCT_PAIRS[cp]
            if p ~= nil then
                if prev_non_ws_is_word then
                    out[#out + 1] = utf8.char(p.ascii)
                else
                    out[#out + 1] = utf8.char(p.full)
                end
                prev_non_ws_is_word = false
            else
                out[#out + 1] = utf8.char(cp)
                prev_non_ws_is_word = is_ascii_word_cp(cp)
            end
        end
    end

    return table.concat(out)
end

-- === Paragraph & chapter formatting ===

local PARA_INDENT = "　　"

-- Chapter title parsing
--
-- NOTE: Lua patterns are byte-based. In particular, putting UTF-8 multibyte characters
-- inside a bracket class like [零一二...] matches *bytes*, not characters.
-- That can lead to false matches and confusing behavior.
--
-- Instead, detect titles using UTF-8 codepoints:
--    第 + (零一二三四五六七八九十百 or 0-9)+ + 章

local function is_chapter_title_number_cp(cp)
    return (cp >= 0x30 and cp <= 0x39) -- 0-9
        or cp == 0x96F6                -- 零
        or cp == 0x4E00                -- 一
        or cp == 0x4E8C                -- 二
        or cp == 0x4E09                -- 三
        or cp == 0x56DB                -- 四
        or cp == 0x4E94                -- 五
        or cp == 0x516D                -- 六
        or cp == 0x4E03                -- 七
        or cp == 0x516B                -- 八
        or cp == 0x4E5D                -- 九
        or cp == 0x5341                -- 十
        or cp == 0x767E                -- 百
end

local function split_chapter_title_prefix(line)
    -- Returns (prefix, rest) when prefix is like "第...章" and rest is remaining text.
    -- Returns (nil, nil) if not a chapter title.
    --
    -- prefix/rest are byte slices based on utf8.codes() byte offsets, so they are safe.
    local cps = {}
    local poses = {}
    for pos, cp in utf8.codes(line) do
        cps[#cps + 1] = cp
        poses[#poses + 1] = pos
    end

    if #cps < 3 then
        return nil, nil
    end

    if cps[1] ~= 0x7B2C then -- 第
        return nil, nil
    end

    local i = 2
    while i <= #cps and is_chapter_title_number_cp(cps[i]) do
        i = i + 1
    end

    if i == 2 then
        return nil, nil
    end

    if i > #cps or cps[i] ~= 0x7AE0 then -- 章
        return nil, nil
    end

    local rest_start = (i < #poses) and poses[i + 1] or (#line + 1)
    local prefix = line:sub(1, rest_start - 1)
    local rest = line:sub(rest_start)

    return prefix, rest
end

local function is_chapter_title(line)
    local prefix, _ = split_chapter_title_prefix(line)

    return prefix ~= nil
end

local function normalize_chapter_title_spacing(line)
    -- Ensure a single ASCII space between "章" and the actual title text.
    -- Example:
    --   "第三章  标题" -> "第三章 标题"
    --   "第三章标题"  -> "第三章 标题"
    --   "第三章" -> "第三章" (no trailing space)
    local prefix, rest = split_chapter_title_prefix(line)
    if not prefix then
        return line
    end

    -- Normalize whatever follows "第...章":
    -- - trim leading ASCII whitespace + full-width spaces
    -- - remove an optional ':' / '：' separator
    -- - trim again
    --
    -- IMPORTANT: avoid Lua pattern classes like "[%s　]" (byte based; can corrupt UTF-8).
    local function trim_leading_spaces_and_optional_colon(rest_text)
        while true do
            local changed = false

            local s2 = rest_text:gsub("^%s+", "")
            if s2 ~= rest_text then
                rest_text = s2
                changed = true
            end

            local indent_end = consume_indent_prefix(rest_text, 1)
            if indent_end > 1 then
                rest_text = rest_text:sub(indent_end)
                changed = true
            end

            if rest_text:sub(1, 1) == ":" then
                rest_text = rest_text:sub(2)
                changed = true
            elseif rest_text:sub(1, 3) == "：" then
                rest_text = rest_text:sub(4)
                changed = true
            end

            if not changed then
                return rest_text
            end
        end
    end

    rest = trim_leading_spaces_and_optional_colon(rest)

    if rest == "" then
        return prefix
    end

    return prefix .. " " .. rest
end

local function starts_with_indent(raw_line)
    -- Detect paragraph starts by indentation before we trim.
    -- Treat ASCII spaces/tabs or full-width space as indentation.
    local next_pos = consume_indent_prefix(raw_line, 1)
    return next_pos > 1 and next_pos <= #raw_line
end

local function join_paragraphs(input)
    input = strip_utf8_bom(input)
    input = normalize_newlines(input)

    local paragraphs = {}
    local current_parts = {}
    local have_current = false
    local current_tail_ascii_word = false

    local function append_to_current(cleaned)
        if not have_current then
            current_parts = { cleaned }
            have_current = true
            current_tail_ascii_word = ends_with_ascii_word(cleaned)

            return
        end

        -- Avoid gluing wrapped English words together.
        if current_tail_ascii_word and starts_with_ascii_word(cleaned) then
            current_parts[#current_parts + 1] = " "
        end
        current_parts[#current_parts + 1] = cleaned
        current_tail_ascii_word = ends_with_ascii_word(cleaned)
    end

    local function flush()
        if have_current and #current_parts > 0 then
            local paragraph = table.concat(current_parts)
            if is_chapter_title(paragraph) then
                paragraphs[#paragraphs + 1] = paragraph
            else
                paragraphs[#paragraphs + 1] = PARA_INDENT .. paragraph
            end
        end
        current_parts = {}
        have_current = false
        current_tail_ascii_word = false
    end

    -- Iterate lines safely (including blank lines). Appending "\n" ensures the last line is included.
    for raw_line in (input .. "\n"):gmatch("([^\n]*)\n") do
        local trimmed = trim_ends(raw_line)
        if trimmed == "" then
            flush()
        else
            if have_current and starts_with_indent(raw_line) then
                flush()
            end

            local cleaned = normalize_punctuation(normalize_whitespace_preserve_english(trimmed))

            if cleaned ~= "" then
                append_to_current(cleaned)
            end
        end
    end

    flush()

    return table.concat(paragraphs, "\n")
end

local function ensure_trailing_blank_lines(out_lines, wanted)
    local count = 0
    for i = #out_lines, 1, -1 do
        if out_lines[i] == "" then
            count = count + 1
        else
            break
        end
    end

    if count > wanted then
        for _ = 1, (count - wanted) do
            out_lines[#out_lines] = nil
        end
    elseif count < wanted then
        for _ = 1, (wanted - count) do
            out_lines[#out_lines + 1] = ""
        end
    end
end

local function format_chapter_titles(text)
    local out_lines = {}
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        if is_chapter_title(line) then
            line = normalize_chapter_title_spacing(line)
            -- Ensure exactly 2 blank lines before the title, except at the very start
            -- of the file (no leading blank lines).
            if #out_lines == 0 then
                ensure_trailing_blank_lines(out_lines, 0)
            else
                ensure_trailing_blank_lines(out_lines, 2)
            end
            out_lines[#out_lines + 1] = line
            -- Ensure exactly 1 blank line after the title.
            ensure_trailing_blank_lines(out_lines, 1)
        else
            -- Preserve existing lines (including blank lines).
            out_lines[#out_lines + 1] = line
        end
    end
    -- Remove trailing blank lines at end of file.
    while #out_lines > 0 and out_lines[#out_lines] == "" do
        out_lines[#out_lines] = nil
    end

    return table.concat(out_lines, "\n")
end

local function replace_corner_quotes(text)
    -- Apply after paragraph/chapter formatting, before quote-level normalization.
    -- Convert curly quotes to corner quotes.
    text = text:gsub("‘", "「")
    text = text:gsub("’", "」")
    text = text:gsub("“", "「")
    text = text:gsub("”", "」")

    return text
end

local function move_trailing_open_quote_to_next_line(text)
    -- Formatting rule:
    -- If a line ends with an opening quote (「 or 『), move that character to the
    -- beginning of the next non-empty line (after any leading indentation).
    local function get_last_codepoint(line_text)
        local last_start = utf8.offset(line_text, -1)
        if last_start == nil then
            return nil, nil
        end

        return utf8.codepoint(line_text, last_start), last_start
    end

    local function is_only_indent(line)
        -- True if line contains only indentation chars: space, tab, or full-width space (U+3000).
        local next_pos = consume_indent_prefix(line, 1)

        return next_pos > #line
    end

    local function split_leading_indent(line)
        -- Split leading indentation consisting of: space, tab, or full-width space (U+3000).
        local next_pos = consume_indent_prefix(line, 1)

        return line:sub(1, next_pos - 1), line:sub(next_pos)
    end

    local lines = {}
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        lines[#lines + 1] = line
    end

    local i = 1
    while i <= (#lines - 1) do
        local line = lines[i]
        local last_cp, last_start = get_last_codepoint(line)

        if last_cp ~= PUNCT_QUOTE_OPEN and last_cp ~= PUNCT_QUOTE_OPEN_NESTED then
            i = i + 1
        else
            local quote = line:sub(last_start)
            local new_line = line:sub(1, last_start - 1)

            -- Find the next non-empty line to receive the quote.
            local j = i + 1
            while j <= #lines and lines[j] == "" do
                j = j + 1
            end

            if j > #lines then
                -- No following non-empty line; keep the quote where it is.
                i = i + 1
            else
                local lead, rest = split_leading_indent(lines[j])
                lines[j] = lead .. quote .. rest
                lines[i] = new_line

                -- If the current line becomes indentation-only, remove it.
                if is_only_indent(lines[i]) then
                    table.remove(lines, i)
                else
                    i = i + 1
                end
            end
        end
    end

    return table.concat(lines, "\n")
end

-- === Quote normalization & validation ===

local function chapter_has_unpaired_quotes(chapter_lines)
    -- Validates both quote levels:
    --   outer: 「 」 (U+300C/U+300D)
    --   inner: 『 』 (U+300E/U+300F)
    local function format_ascii_preview(line_text, limit)
        limit = limit or 160
        local n = math.min(#line_text, limit)
        local bytes = { line_text:byte(1, n) }
        local out = {}
        for _, b in ipairs(bytes) do
            if b >= 0x20 and b <= PUNCT_ASCII_TILDE then
                out[#out + 1] = string.char(b)
            else
                out[#out + 1] = "."
            end
        end
        if #line_text > limit then
            out[#out + 1] = "..."
        end

        return table.concat(out)
    end

    local function format_hex_dump_around(line_text, pos)
        local start_pos = math.max(1, pos - 16)
        local end_pos = math.min(#line_text, pos + 16)
        local bytes = { line_text:byte(start_pos, end_pos) }
        local parts = {}
        for i, b in ipairs(bytes) do
            parts[#parts + 1] = string.format("%02X", b)
        end

        return string.format("bytes %d..%d: %s", start_pos, end_pos, table.concat(parts, " "))
    end

    local stack = {}
    for line_index, line in ipairs(chapter_lines) do
        local _, invalid_pos = utf8.len(line)
        if invalid_pos ~= nil then
            local chapter_title = chapter_lines[1] or "<unknown chapter>"
            local line_kind = (line_index == 1) and "title" or "body"
            io.stderr:write("Invalid UTF-8 detected. \n")
            io.stderr:write("Chapter title: " .. tostring(chapter_title) .. "\n")
            io.stderr:write(string.format("Offending line: %s (chapter-local index %d)\n", line_kind, line_index))
            io.stderr:write(string.format("Invalid byte position in that line: %d\n", invalid_pos))
            io.stderr:write("Line preview (ASCII; non-ASCII shown as '.'): " .. format_ascii_preview(line) .. "\n")
            io.stderr:write("Hex dump around invalid byte: " .. format_hex_dump_around(line, invalid_pos) .. "\n")
            die("Aborting due to invalid UTF-8.")
        end

        for _, cp in utf8.codes(line) do
            if cp == PUNCT_QUOTE_OPEN or cp == PUNCT_QUOTE_OPEN_NESTED then
                stack[#stack + 1] = cp
            elseif cp == PUNCT_QUOTE_CLOSE or cp == PUNCT_QUOTE_CLOSE_NESTED then
                local open = stack[#stack]
                stack[#stack] = nil
                if open == nil then
                    return true
                end

                if cp == PUNCT_QUOTE_CLOSE and open ~= PUNCT_QUOTE_OPEN then
                    return true
                end

                if cp == PUNCT_QUOTE_CLOSE_NESTED and open ~= PUNCT_QUOTE_OPEN_NESTED then
                    return true
                end
            end
        end
    end

    return #stack ~= 0
end

local function normalize_quote_levels_in_lines(lines)
    -- Normalize quote levels by nesting depth:
    -- - depth 0: use 「 」
    -- - depth >= 1: use 『 』
    -- This also fixes the case where 『』 is incorrectly used as the first-level quote.
    local depth = 0
    local out = {}
    for _, line in ipairs(lines) do
        local buf = {}
        for _, cp in utf8.codes(line) do
            if cp == PUNCT_QUOTE_OPEN or cp == PUNCT_QUOTE_OPEN_NESTED then
                if depth == 0 then
                    buf[#buf + 1] = utf8.char(PUNCT_QUOTE_OPEN)        -- 「
                else
                    buf[#buf + 1] = utf8.char(PUNCT_QUOTE_OPEN_NESTED) -- 『
                end
                depth = depth + 1
            elseif cp == PUNCT_QUOTE_CLOSE or cp == PUNCT_QUOTE_CLOSE_NESTED then
                -- Only call this for chapters that are already validated.
                if depth == 1 then
                    buf[#buf + 1] = utf8.char(PUNCT_QUOTE_CLOSE)        -- 」
                else
                    buf[#buf + 1] = utf8.char(PUNCT_QUOTE_CLOSE_NESTED) -- 』
                end
                depth = depth - 1
            else
                buf[#buf + 1] = utf8.char(cp)
            end
        end
        out[#out + 1] = table.concat(buf)
    end

    return out
end


local function normalize_quote_levels_in_ok_chapters(text)
    -- Process chapter-by-chapter. If a chapter has no pairing issue, normalize quote levels:
    -- outer -> 「」, inner -> 『』.
    local out_lines = {}
    local current_title = nil
    local chapter_lines = {}

    local function flush_chapter()
        if current_title == nil then
            return
        end

        local has_issue = chapter_has_unpaired_quotes(chapter_lines)
        local final_lines = chapter_lines
        if not has_issue then
            final_lines = normalize_quote_levels_in_lines(chapter_lines)
        end

        for _, l in ipairs(final_lines) do
            out_lines[#out_lines + 1] = l
        end

        current_title = nil
        chapter_lines = {}
    end

    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        if is_chapter_title(line) then
            flush_chapter()
            current_title = line
            chapter_lines = { line }
        else
            if current_title ~= nil then
                chapter_lines[#chapter_lines + 1] = line
            else
                out_lines[#out_lines + 1] = line
            end
        end
    end

    flush_chapter()

    return table.concat(out_lines, "\n")
end

local function check_paragraph_punctuation(text)
    -- Check that paragraphs:
    -- 1. End with valid punctuation: ， 。 ？ ！ … , . ? !
    -- 2. If ends with 』 」 ）, strip them and check what's underneath - must follow rule 1
    -- 3. If second-to-last is still 』 」 ）, keep stripping and check what's underneath
    -- 4. Don't start with ， 。 ？ ！ 」 』 … or , . ? !
    -- Returns: table of issues

    -- Character sets (using global constants)
    local valid_ending_punct = {
        [PUNCT_ASCII_COMMA] = true,              -- ,
        [PUNCT_ASCII_PERIOD] = true,             -- .
        [PUNCT_ASCII_QUESTION] = true,           -- ?
        [PUNCT_ASCII_EXCLAIM] = true,            -- !
        [PUNCT_ASCII_COLON] = true,              -- :
        [PUNCT_ASCII_TILDE] = true,              -- ~
        [PUNCT_EM_DASH] = true,                  -- —
        [PUNCT_COMMA_CN] = true,                 -- ，
        [PUNCT_END_PERIOD] = true,               -- 。
        [PUNCT_END_QUESTION] = true,             -- ？
        [PUNCT_END_EXCLAIM] = true,              -- ！
        [PUNCT_TILDE_CN] = true,                 -- ～
        [PUNCT_COLON_CN] = true,                 -- ：
        [PUNCT_SEMICOLON_CN] = true,             -- ；
        [PUNCT_ELLIPSIS] = true,                 -- …
        [PUNCT_DOUBLE_ANGLE_QUOTE_CLOSE] = true, -- 》
    }

    local closing_quotes = {
        [PUNCT_QUOTE_CLOSE] = true,        -- 」
        [PUNCT_QUOTE_CLOSE_NESTED] = true, -- 』
        [PUNCT_BRACKET_CLOSE_CN] = true,   -- 】
        [PUNCT_PAREN_CLOSE_CN] = true,     -- ）
    }

    -- invalid_start_punct = valid_ending_punct + closing_quotes
    local invalid_start_punct = {}
    for cp, _ in pairs(valid_ending_punct) do
        invalid_start_punct[cp] = true
    end

    for cp, _ in pairs(closing_quotes) do
        invalid_start_punct[cp] = true
    end

    local issues = {}

    local function is_valid_ending(cp)
        return valid_ending_punct[cp] ~= nil
    end

    local function is_closing_quote(cp)
        return closing_quotes[cp] ~= nil
    end

    local function is_paragraph_start_invalid(cp)
        return invalid_start_punct[cp] ~= nil
    end

    local line_no = 0
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        line_no = line_no + 1

        -- Skip empty lines and chapter titles
        if line:match("%S") and not is_chapter_title(line) then
            local trimmed = trim_ends(line)

            if #trimmed > 0 then
                -- Collect all codepoints for easier access
                local cps = {}
                for _, cp in utf8.codes(trimmed) do
                    cps[#cps + 1] = cp
                end

                if #cps > 0 then
                    -- Check paragraph ending: skip trailing closing quotes/parens, check what's underneath
                    local last_idx = #cps
                    while last_idx > 0 and is_closing_quote(cps[last_idx]) do
                        last_idx = last_idx - 1
                    end

                    if last_idx > 0 then
                        local actual_last_cp = cps[last_idx]
                        if not is_valid_ending(actual_last_cp) then
                            issues[#issues + 1] = {
                                line_no = line_no,
                                kind = "invalid_ending",
                                note = "paragraph ends with invalid punctuation"
                            }
                        end
                    end
                end

                -- Check paragraph starting
                local first_cp = cps[1]
                if first_cp ~= nil and is_paragraph_start_invalid(first_cp) then
                    issues[#issues + 1] = {
                        line_no = line_no,
                        kind = "invalid_start",
                        note = "paragraph starts with invalid punctuation"
                    }
                end
            end
        end
    end

    return issues
end

local function log_path_for_output(output_path)
    local sep = package.config:sub(1, 1)
    local dir = output_path:match("^(.*)[\\/][^\\/]+$")
    if not dir then
        return "log"
    end

    return dir .. sep .. "log"
end

local function first_quote_issue_in_chapter(chapter_line_items)
    -- chapter_line_items: { { line_no = <int>, text = <string> }, ... }
    -- Returns:
    --   nil if OK
    --   { kind = <string>, line_no = <int>, note = <string> }
    -- Track both the opening codepoint and the line number where it occurred.
    local stack = {}
    for _, item in ipairs(chapter_line_items) do
        local line_no = item.line_no
        local text = item.text
        for _, cp in utf8.codes(text) do
            if cp == PUNCT_QUOTE_OPEN or cp == PUNCT_QUOTE_OPEN_NESTED then
                stack[#stack + 1] = { cp = cp, line_no = line_no }
            elseif cp == PUNCT_QUOTE_CLOSE or cp == PUNCT_QUOTE_CLOSE_NESTED then
                local open = stack[#stack]
                stack[#stack] = nil
                if open == nil then
                    return { kind = "extra_close", line_no = line_no, note = "closing quote without opener" }
                end

                if cp == PUNCT_QUOTE_CLOSE and open.cp ~= PUNCT_QUOTE_OPEN then
                    return { kind = "mismatch", line_no = line_no, note = "expected 』 but found 」" }
                end

                if cp == PUNCT_QUOTE_CLOSE_NESTED and open.cp ~= PUNCT_QUOTE_OPEN_NESTED then
                    return { kind = "mismatch", line_no = line_no, note = "expected 」 but found 』" }
                end
            end
        end
    end

    if #stack ~= 0 then
        -- Report the line number of the last unmatched opening quote (the one still on the stack).
        local last_open = stack[#stack]
        local open_line_no = last_open and last_open.line_no or 0

        return { kind = "unclosed", line_no = open_line_no, note = "unclosed opening quote(s) by end of chapter" }
    end

    return nil
end

local function write_unpaired_quote_log(text, output_path)
    -- Split output into chapters, validate quotes per chapter, and include output line numbers.
    local current_title = nil
    local current_title_line_no = 0
    local current_items = {}
    local issues = {}

    local function flush_chapter()
        if current_title ~= nil then
            local issue = first_quote_issue_in_chapter(current_items)
            if issue ~= nil then
                issues[#issues + 1] = {
                    title = current_title,
                    title_line_no = current_title_line_no,
                    issue = issue,
                }
            end
        end
        current_items = {}
    end

    local line_no = 0
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        line_no = line_no + 1
        if is_chapter_title(line) then
            flush_chapter()
            current_title = line
            current_title_line_no = line_no
            current_items = { { line_no = line_no, text = line } }
        else
            if current_title ~= nil then
                current_items[#current_items + 1] = { line_no = line_no, text = line }
            end
        end
    end

    flush_chapter()

    local log_path = log_path_for_output(output_path)
    delete_file_if_exists(log_path)

    local lines = {}
    if #issues > 0 then
        lines[#lines + 1] = "Unpaired/mismatched quotes detected (line numbers are in the output file):"
        for _, item in ipairs(issues) do
            lines[#lines + 1] = string.format("- Chapter at line %d: %s", item.title_line_no, item.title)
            lines[#lines + 1] = string.format(
                "  First issue at line %d (%s): %s",
                item.issue.line_no,
                item.issue.kind,
                item.issue.note
            )
        end
    end

    write_all(log_path, table.concat(lines, "\n"))

    -- If we wrote any log lines, notify the user on the terminal.
    if #lines > 0 then
        io.stderr:write("Quote issues detected; see log at: " .. tostring(log_path) .. "\n")
    end
end

local function write_paragraph_check_log(text, output_path)
    -- Check paragraphs for punctuation issues
    local issues = check_paragraph_punctuation(text)

    local log_path = log_path_for_output(output_path)

    local lines = {}
    if #issues > 0 then
        -- Read existing log if it has quote issues
        local existing = file_exists(log_path) and read_all(log_path) or ""
        if #existing > 0 then
            lines[#lines + 1] = existing
            lines[#lines + 1] = ""
        end

        lines[#lines + 1] = "Paragraph punctuation issues detected (line numbers are in the output file):"
        for _, issue in ipairs(issues) do
            lines[#lines + 1] = string.format("- Line %d (%s): %s", issue.line_no, issue.kind, issue.note)
        end
    end

    if #lines > 0 then
        write_all(log_path, table.concat(lines, "\n"))
        io.stderr:write("Paragraph issues detected; see log at: " .. tostring(log_path) .. "\n")
    end
end

-- === CLI ===

local function parse_args(argv)
    local args = {}
    if #argv == 0 then
        args.help = true
        return args
    end

    if argv[1] == "--help" or argv[1] == "-h" then
        args.help = true
        return args
    end

    if argv[1]:sub(1, 1) == "-" then
        die("Unknown argument: " .. tostring(argv[1]))
    end

    if #argv > 1 then
        die("Only one argument is allowed: <input>")
    end

    args.input = argv[1]

    return args
end

local function backup_original_path(input_path)
    local sep = package.config:sub(1, 1)
    local dir, file = input_path:match("^(.*[\\/])(.*)$")
    if not dir then
        dir = ""
        file = input_path
    end

    local base = file:gsub("%.[^.]*$", "")
    if base == "" then
        base = file
    end

    local prefix = "original_" .. base .. ".txt"
    if dir == "" then
        return prefix
    end

    local normalized_dir = dir:gsub("[\\/]$", "")

    return normalized_dir .. sep .. prefix
end

local function main()
    local args = parse_args(arg)
    if args.help or not args.input then
        io.write([[Usage:
	lua .\noval_formatter.lua <input>

Output:
	- Writes a backup of the original input as original_<input> (only if not exists)
    - Writes formatted output to <input> (overwritten)
	- log next to the output (overwritten each run)
]])
        return
    end

    args.output = args.input
    args.original = backup_original_path(args.input)

    local input = read_all(args.input)
    if not file_exists(args.original) then
        write_all(args.original, input)
    end

    local output = join_paragraphs(input)
    output = format_chapter_titles(output)
    output = replace_corner_quotes(output)
    output = normalize_quote_levels_in_ok_chapters(output)
    output = move_trailing_open_quote_to_next_line(output)
    write_all(args.output, output)

    -- Run checks against the on-disk output so checks always reflect the final file.
    local written_output = read_all(args.output)
    written_output = strip_utf8_bom(written_output)
    written_output = normalize_newlines(written_output)
    write_unpaired_quote_log(written_output, args.output)
    write_paragraph_check_log(written_output, args.output)
end

main()

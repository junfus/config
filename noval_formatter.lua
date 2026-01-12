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
    -- Consume leading indentation (spaces, tabs, full-width spaces) from position start_pos.
    -- Returns position after last indentation character.
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

local function split_lines(text)
    -- Split text into lines, appending newline ensures last line is captured
    local lines = {}
    for line in (text .. "\n"):gmatch("([^\n]*)\n") do
        lines[#lines + 1] = line
    end
    return lines
end

local function is_ascii_word_cp(cp)
    return (cp >= 0x30 and cp <= 0x39) -- 0-9
        or (cp >= 0x41 and cp <= 0x5A) -- A-Z
        or (cp >= 0x61 and cp <= 0x7A) -- a-z
        or (cp == 0x5F)                -- _
end

-- === Whitespace normalization helpers ===

local function is_whitespace_cp(cp)
    return cp == 0x20 or cp == 0x09 or cp == 0x3000
end

local function normalize_whitespace_preserve_english(line)
    -- Preserve a single ASCII space only when it separates ASCII word characters.
    -- Remove other whitespace (including full-width spaces) between CJK and punctuation.
    local codepoints = {}
    for _, cp in utf8.codes(line) do
        codepoints[#codepoints + 1] = cp
    end

    local out = {}
    local i = 1
    while i <= #codepoints do
        local cp = codepoints[i]
        if is_whitespace_cp(cp) then
            -- find nearest non-space to the left
            local l = i - 1
            while l >= 1 and is_whitespace_cp(codepoints[l]) do l = l - 1 end
            local r = i + 1
            while r <= #codepoints and is_whitespace_cp(codepoints[r]) do r = r + 1 end

            if l >= 1 and r <= #codepoints and is_ascii_word_cp(codepoints[l]) and is_ascii_word_cp(codepoints[r]) then
                if out[#out] ~= " " then out[#out + 1] = " " end
            end

            i = r
        else
            out[#out + 1] = utf8.char(cp)
            i = i + 1
        end
    end

    return table.concat(out)
end

local function normalize_fullwidth_to_ascii(line)
    -- Convert full-width ASCII characters to ASCII (A-Za-z0-9).
    local out = {}
    for _, cp in utf8.codes(line) do
        if cp >= 0xFF10 and cp <= 0xFF19
            or cp >= 0xFF21 and cp <= 0xFF3A
            or cp >= 0xFF41 and cp <= 0xFF5A then
            out[#out + 1] = utf8.char(cp - 0xFF01 + 0x21)
        else
            out[#out + 1] = utf8.char(cp)
        end
    end

    return table.concat(out)
end

local function ends_with_ascii_word(text)
    -- Check if text ends with ASCII word character (letter, digit, or underscore).
    return text:match("[A-Za-z0-9_]$") ~= nil
end

local function starts_with_ascii_word(text)
    -- Check if text starts with ASCII word character (letter, digit, or underscore).
    return text:match("^[A-Za-z0-9_]") ~= nil
end

local PUNCT_PAIRS = {
    -- Maps punctuation codepoints to {ascii, full-width} form pair.
    -- Used to normalize punctuation based on context (English word vs Chinese text).
    [0x21] = { ascii = 0x21, full = 0xFF01 },   -- ! / ！
    [0xFF01] = { ascii = 0x21, full = 0xFF01 }, -- ！ / !
    [0x28] = { ascii = 0x28, full = 0xFF08 },   -- ( / （
    [0xFF08] = { ascii = 0x28, full = 0xFF08 }, -- （ / (
    [0x29] = { ascii = 0x29, full = 0xFF09 },   -- ) / ）
    [0xFF09] = { ascii = 0x29, full = 0xFF09 }, -- ） / )
    [0x2C] = { ascii = 0x2C, full = 0xFF0C },   -- , / ，
    [0xFF0C] = { ascii = 0x2C, full = 0xFF0C }, -- ， / ,
    [0x2E] = { ascii = 0x2E, full = 0x3002 },   -- . / 。
    [0x3002] = { ascii = 0x2E, full = 0x3002 }, -- 。 / .
    [0x3F] = { ascii = 0x3F, full = 0xFF1F },   -- ? / ？
    [0xFF1F] = { ascii = 0x3F, full = 0xFF1F }, -- ？ / ?
    [0x3A] = { ascii = 0x3A, full = 0xFF1A },   -- : / ：
    [0xFF1A] = { ascii = 0x3A, full = 0xFF1A }, -- ： / :
    [0x3B] = { ascii = 0x3B, full = 0xFF1B },   -- ; / ；
    [0xFF1B] = { ascii = 0x3B, full = 0xFF1B }, -- ； / ;
    [0x5B] = { ascii = 0x5B, full = 0xFF3B },   -- [ / ［
    [0xFF3B] = { ascii = 0x5B, full = 0xFF3B }, -- ［ / [
    [0x5D] = { ascii = 0x5D, full = 0xFF3D },   -- ] / ］
    [0xFF3D] = { ascii = 0x5D, full = 0xFF3D }, -- ］ / ]
    [0x7B] = { ascii = 0x7B, full = 0xFF5B },   -- { / ｛
    [0xFF5B] = { ascii = 0x7B, full = 0xFF5B }, -- ｛ / {
    [0x7D] = { ascii = 0x7D, full = 0xFF5D },   -- } / ｝
    [0xFF5D] = { ascii = 0x7D, full = 0xFF5D }, -- ｝ / }
    [0x7E] = { ascii = 0x7E, full = 0xFF5E },   -- ~ / ～
    [0xFF5E] = { ascii = 0x7E, full = 0xFF5E }, -- ～ / ~
}

local function normalize_punctuation(line)
    -- Normalize punctuation for mixed Chinese/English text.
    -- Choose ASCII punctuation when it follows an ASCII word; otherwise use full-width.
    local out = {}
    local last_ascii = false
    for _, cp in utf8.codes(line) do
        if cp == 0x20 or cp == 0x09 then
            out[#out + 1] = utf8.char(cp)
            -- preserve last_ascii
        else
            local pair = PUNCT_PAIRS[cp]
            if pair then
                out[#out + 1] = utf8.char(last_ascii and pair.ascii or pair.full)
                last_ascii = false
            else
                out[#out + 1] = utf8.char(cp)
                last_ascii = is_ascii_word_cp(cp)
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
-- Supported patterns:
--   第 + (零一二三四五六七八九十百 or 0-9)+ + 章
--   番外 (Extra/Special chapter, optionally followed by title)

local function is_chapter_title_number_cp(cp)
    -- Check if codepoint is a valid chapter number digit (0-9 or Chinese numerals).
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
        or cp == 0x5343                -- 千
        or cp == 0x4E07                -- 万
end

-- === Chapter title parsing helpers ===

local function collect_codepoints_and_positions(text)
    -- Helper: Extract both codepoints and their byte positions for safe UTF-8 slicing.
    local codepoints = {}
    local byte_positions = {}
    for byte_pos, codepoint in utf8.codes(text) do
        codepoints[#codepoints + 1] = codepoint
        byte_positions[#byte_positions + 1] = byte_pos
    end
    return codepoints, byte_positions
end

local function try_pattern_prologue_chapter(codepoints, byte_positions, text)
    -- Try to match "楔子" (extra/special chapter) pattern.
    if codepoints[1] == 0x6954 and #codepoints >= 2 and codepoints[2] == 0x5B50 then
        local rest_start = (3 <= #byte_positions) and byte_positions[3] or (#text + 1)
        local prefix = text:sub(1, rest_start - 1)
        local rest = text:sub(rest_start)
        return prefix, rest
    end
    return nil, nil
end

local function try_pattern_extra_chapter(codepoints, byte_positions, text)
    -- Try to match "番外" (extra/special chapter) pattern.
    if codepoints[1] == 0x756A and #codepoints >= 2 and codepoints[2] == 0x5916 then
        local rest_start = (3 <= #byte_positions) and byte_positions[3] or (#text + 1)
        local prefix = text:sub(1, rest_start - 1)
        local rest = text:sub(rest_start)
        return prefix, rest
    end
    return nil, nil
end

local function try_pattern_numbered_chapter(codepoints, byte_positions, text)
    -- Try to match "第...章" (numbered chapter) pattern where ... is chapter number.
    if #codepoints < 3 or codepoints[1] ~= 0x7B2C then -- 第
        return nil, nil
    end

    -- Scan for chapter number digits
    local i = 2
    while i <= #codepoints and is_chapter_title_number_cp(codepoints[i]) do
        i = i + 1
    end

    -- Must have at least one digit and then 章
    if i == 2 or i > #codepoints or codepoints[i] ~= 0x7AE0 then -- 章
        return nil, nil
    end

    local rest_start = (i < #byte_positions) and byte_positions[i + 1] or (#text + 1)
    local prefix = text:sub(1, rest_start - 1)
    local rest = text:sub(rest_start)
    return prefix, rest
end

local function split_chapter_title_prefix(line)
    -- Returns (prefix, rest) when prefix is like "第...章" or "番外" and rest is remaining text.
    -- Returns (nil, nil) if not a chapter title.
    --
    -- prefix/rest are byte slices based on utf8.codes() byte offsets, so they are safe.

    local codepoints, byte_positions = collect_codepoints_and_positions(line)

    if #codepoints == 0 then
        return nil, nil
    end

    -- Try patterns in order: 楔子, 番外, then 第...章
    local prefix, rest = try_pattern_prologue_chapter(codepoints, byte_positions, line)
    if prefix ~= nil then
        return prefix, rest
    end

    local prefix, rest = try_pattern_extra_chapter(codepoints, byte_positions, line)
    if prefix ~= nil then
        return prefix, rest
    end

    return try_pattern_numbered_chapter(codepoints, byte_positions, line)
end

local function is_chapter_title(line)
    -- Detect if line is a chapter title (matches 楔子, 番外, or 第...章 pattern).
    local prefix, _ = split_chapter_title_prefix(line)

    return prefix ~= nil
end

local function is_separator(line)
    -- Check if line is a separator (exactly 6 dashes: "------").
    -- Allow only dash character (0x2D) repeated exactly 6 times, with optional surrounding whitespace.
    local trimmed = trim_ends(line)
    if #trimmed ~= 6 then
        return false
    end
    for _, cp in utf8.codes(trimmed) do
        if cp ~= 0x2D then -- 0x2D is dash '-'
            return false
        end
    end
    return true
end

-- === Chapter title spacing helpers ===

local function trim_title_suffix(text)
    -- Remove leading ASCII/UTF-8 whitespace and a single leading colon (ASCII or full-width).
    -- Repeats until no more change (handles multiple separator characters in sequence).
    while true do
        local before = text

        -- Trim ASCII whitespace
        text = text:gsub("^%s+", "")

        -- Trim leading full-width spaces (consume_indent_prefix handles them)
        local indent_end_pos = consume_indent_prefix(text, 1)
        if indent_end_pos > 1 then
            text = text:sub(indent_end_pos)
        end

        -- Remove a single leading ASCII colon ':' or a full-width colon '：'
        if text:sub(1, 1) == ":" then
            text = text:sub(2)
        elseif text:sub(1, 3) == "：" then
            text = text:sub(4)
        end

        if text == before then
            return text
        end
    end
end

local function normalize_chapter_title_spacing(line)
    -- Ensure proper spacing for chapter titles:
    --   "第三章  标题" -> "第三章 标题" (single space after 章)
    --   "第三章标题"  -> "第三章 标题" (add space if missing)
    --   "第三章" -> "第三章" (no trailing space)
    --   "番外  标题" -> "番外 标题" (single space after 番外)
    --   "番外标题" -> "番外 标题" (add space if missing)
    --   "番外" -> "番外" (no trailing space)

    local prefix, rest = split_chapter_title_prefix(line)
    if not prefix then
        return line
    end

    rest = trim_title_suffix(rest)

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

-- === Paragraph joining helpers ===

local function normalize_line_text(text)
    -- Apply all text normalizations to a line before adding to current paragraph.
    -- Whitespace preservation must happen before punctuation normalization.
    local normalized = normalize_whitespace_preserve_english(text)
    normalized = normalize_fullwidth_to_ascii(normalized)
    return normalize_punctuation(normalized)
end

local function should_add_space_before_text(current_ends_with_ascii_word, new_text)
    -- Determine if space is needed before new text.
    -- Space is needed when joining two ASCII word chunks to prevent gluing.
    return current_ends_with_ascii_word and starts_with_ascii_word(new_text)
end

local function format_paragraph_for_output(text)
    -- Format paragraph: add indentation unless it's a chapter title.
    if is_chapter_title(text) then
        return text
    end
    return PARA_INDENT .. text
end

local function join_paragraphs(input)
    input = strip_utf8_bom(input)
    input = normalize_newlines(input)

    -- State tracking during paragraph assembly
    local paragraphs = {}
    local current_paragraph_parts = {}
    local has_current_paragraph = false
    local current_ends_with_ascii_word = false

    -- Process each line from input
    local lines = split_lines(input)
    for _, raw_line in ipairs(lines) do
        -- Handle separator lines (exactly 6 dashes)
        if is_separator(raw_line) then
            if has_current_paragraph and #current_paragraph_parts > 0 then
                local paragraph = table.concat(current_paragraph_parts)
                local formatted = format_paragraph_for_output(paragraph)
                paragraphs[#paragraphs + 1] = formatted
            end
            current_paragraph_parts = {}
            has_current_paragraph = false
            current_ends_with_ascii_word = false
            paragraphs[#paragraphs + 1] = PARA_INDENT .. trim_ends(raw_line)
        else
            local trimmed = trim_ends(raw_line)
            -- Blank/empty lines trigger paragraph boundaries
            if trimmed == "" then
                if has_current_paragraph and #current_paragraph_parts > 0 then
                    local paragraph = table.concat(current_paragraph_parts)
                    local formatted = format_paragraph_for_output(paragraph)
                    paragraphs[#paragraphs + 1] = formatted
                end
                current_paragraph_parts = {}
                has_current_paragraph = false
                current_ends_with_ascii_word = false
            else
                -- Indented lines also trigger paragraph boundaries
                if has_current_paragraph and starts_with_indent(raw_line) then
                    if #current_paragraph_parts > 0 then
                        local paragraph = table.concat(current_paragraph_parts)
                        local formatted = format_paragraph_for_output(paragraph)
                        paragraphs[#paragraphs + 1] = formatted
                    end
                    current_paragraph_parts = {}
                    has_current_paragraph = false
                    current_ends_with_ascii_word = false
                end

                -- Normalize and add line text
                local cleaned = normalize_line_text(trimmed)
                if cleaned ~= "" then
                    if not has_current_paragraph then
                        -- Starting first chunk of paragraph
                        current_paragraph_parts = { cleaned }
                        has_current_paragraph = true
                        current_ends_with_ascii_word = ends_with_ascii_word(cleaned)
                    else
                        -- Avoid gluing wrapped English words together
                        if should_add_space_before_text(current_ends_with_ascii_word, cleaned) then
                            current_paragraph_parts[#current_paragraph_parts + 1] = " "
                        end
                        current_paragraph_parts[#current_paragraph_parts + 1] = cleaned
                        current_ends_with_ascii_word = ends_with_ascii_word(cleaned)
                    end
                end
            end
        end
    end

    -- Don't forget final paragraph
    if has_current_paragraph and #current_paragraph_parts > 0 then
        local paragraph = table.concat(current_paragraph_parts)
        local formatted = format_paragraph_for_output(paragraph)
        paragraphs[#paragraphs + 1] = formatted
    end

    return table.concat(paragraphs, "\n")
end

local function ensure_trailing_blank_lines(output_lines, desired_count)
    -- Adjust trailing blank lines in output array to match desired count.
    local current_count = 0
    for i = #output_lines, 1, -1 do
        if output_lines[i] == "" then
            current_count = current_count + 1
        else
            break
        end
    end

    if current_count > desired_count then
        for _ = 1, (current_count - desired_count) do
            output_lines[#output_lines] = nil
        end
    elseif current_count < desired_count then
        for _ = 1, (desired_count - current_count) do
            output_lines[#output_lines + 1] = ""
        end
    end
end

local function format_chapter_titles(text)
    local output_lines = {}
    local lines = split_lines(text)
    for _, line in ipairs(lines) do
        if is_chapter_title(line) then
            line = normalize_chapter_title_spacing(line)
            -- Ensure exactly 2 blank lines before title (except at file start).
            if #output_lines == 0 then
                ensure_trailing_blank_lines(output_lines, 0)
            else
                ensure_trailing_blank_lines(output_lines, 2)
            end
            output_lines[#output_lines + 1] = line
            -- Ensure exactly 1 blank line after the title.
            ensure_trailing_blank_lines(output_lines, 1)
        else
            -- Preserve existing lines (including blank lines).
            output_lines[#output_lines + 1] = line
        end
    end
    -- Remove trailing blank lines at end of file.
    while #output_lines > 0 and output_lines[#output_lines] == "" do
        output_lines[#output_lines] = nil
    end

    return table.concat(output_lines, "\n")
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

-- === Quote movement helpers ===

local function get_last_codepoint(line_text)
    -- Extract the last UTF-8 codepoint from line and its byte position.
    local last_byte_pos = utf8.offset(line_text, -1)
    if last_byte_pos == nil then
        return nil, nil
    end

    return utf8.codepoint(line_text, last_byte_pos), last_byte_pos
end

local function is_only_indent(line)
    -- Check if line contains only indentation (spaces, tabs, full-width space).
    local next_pos = consume_indent_prefix(line, 1)

    return next_pos > #line
end

local function split_leading_indent(line)
    -- Split line into (indentation, content) parts.
    local next_pos = consume_indent_prefix(line, 1)

    return line:sub(1, next_pos - 1), line:sub(next_pos)
end

local function move_trailing_open_quote_to_next_line(text)
    -- Formatting rule:
    -- If a line ends with an opening quote (「 or 『), move that character to the
    -- beginning of the next non-empty line (after any leading indentation).

    local lines = split_lines(text)

    local i = 1
    while i <= (#lines - 1) do
        local line = lines[i]
        local last_cp, last_byte_pos = get_last_codepoint(line)

        if last_cp ~= 0x300C and last_cp ~= 0x300E then -- opening quotes: 「 or 『
            i = i + 1
        else
            local quote_char = line:sub(last_byte_pos)
            local line_without_quote = line:sub(1, last_byte_pos - 1)

            -- Find the next non-empty line to receive the quote.
            local j = i + 1
            while j <= #lines and lines[j] == "" do
                j = j + 1
            end

            if j > #lines then
                -- No following non-empty line; keep the quote where it is.
                i = i + 1
            else
                local indent_part, content_part = split_leading_indent(lines[j])
                lines[j] = indent_part .. quote_char .. content_part
                lines[i] = line_without_quote

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

-- === UTF-8 validation helpers ===

local function format_ascii_preview(text, limit)
    limit = limit or 160
    local preview_len = math.min(#text, limit)
    local preview_bytes = { text:byte(1, preview_len) }
    local preview_chars = {}
    for _, byte_val in ipairs(preview_bytes) do
        if byte_val >= 0x20 and byte_val <= 0x7E then
            preview_chars[#preview_chars + 1] = string.char(byte_val)
        else
            preview_chars[#preview_chars + 1] = "."
        end
    end
    if #text > limit then
        preview_chars[#preview_chars + 1] = "..."
    end
    return table.concat(preview_chars)
end

local function format_hex_around_byte(text, byte_pos)
    local start = math.max(1, byte_pos - 16)
    local finish = math.min(#text, byte_pos + 16)
    local hex_bytes = { text:byte(start, finish) }
    local hex_strs = {}
    for _, b in ipairs(hex_bytes) do
        hex_strs[#hex_strs + 1] = string.format("%02X", b)
    end
    return string.format("bytes %d..%d: %s", start, finish, table.concat(hex_strs, " "))
end

local function validate_utf8_in_chapter(chapter_lines)
    -- Check for invalid UTF-8 in chapter lines. If found, report error and abort.
    -- Returns nil if all valid.
    for line_idx, line in ipairs(chapter_lines) do
        local _, invalid_byte_pos = utf8.len(line)
        if invalid_byte_pos == nil then
            goto continue_line
        end

        -- UTF-8 error detected - format detailed error message
        local chapter_title = chapter_lines[1] or "<unknown chapter>"
        local line_kind = (line_idx == 1) and "title" or "body"

        io.stderr:write("Invalid UTF-8 detected. \n")
        io.stderr:write("Chapter title: " .. tostring(chapter_title) .. "\n")
        io.stderr:write(string.format("Offending line: %s (chapter-local index %d)\n", line_kind, line_idx))
        io.stderr:write(string.format("Invalid byte position in that line: %d\n", invalid_byte_pos))
        io.stderr:write("Line preview (ASCII; non-ASCII shown as '.'): " .. format_ascii_preview(line) .. "\n")
        io.stderr:write("Hex dump around invalid byte: " .. format_hex_around_byte(line, invalid_byte_pos) .. "\n")
        die("Aborting due to invalid UTF-8.")

        ::continue_line::
    end
end

local function chapter_has_unpaired_quotes(chapter_lines)
    -- Validates both quote levels:
    --   outer: 「 」 (U+300C/U+300D)
    --   inner: 『 』 (U+300E/U+300F)
    validate_utf8_in_chapter(chapter_lines)

    local quote_stack = {}
    for _, line in ipairs(chapter_lines) do
        for _, codepoint in utf8.codes(line) do
            if codepoint == 0x300C or codepoint == 0x300E then     -- opening quotes: 「 or 『
                quote_stack[#quote_stack + 1] = codepoint
            elseif codepoint == 0x300D or codepoint == 0x300F then -- closing quotes: 」 or 』
                local opening_quote = quote_stack[#quote_stack]
                quote_stack[#quote_stack] = nil
                if opening_quote == nil then
                    return true
                end

                if codepoint == 0x300D and opening_quote ~= 0x300C then -- 」 but expected 「
                    return true
                end

                if codepoint == 0x300F and opening_quote ~= 0x300E then -- 』 but expected 『
                    return true
                end
            end
        end
    end

    return #quote_stack ~= 0
end

local function normalize_quote_levels_in_lines(lines)
    -- Normalize quote levels by nesting depth:
    -- - depth 0: use 「 」
    -- - depth >= 1: use 『 』
    -- This also fixes the case where 『』 is incorrectly used as the first-level quote.
    local quote_depth = 0
    local output_lines = {}
    for _, line in ipairs(lines) do
        local line_buffer = {}
        for _, codepoint in utf8.codes(line) do
            if codepoint == 0x300C or codepoint == 0x300E then        -- opening quotes: 「 or 『
                if quote_depth == 0 then
                    line_buffer[#line_buffer + 1] = utf8.char(0x300C) -- 「
                else
                    line_buffer[#line_buffer + 1] = utf8.char(0x300E) -- 『
                end
                quote_depth = quote_depth + 1
            elseif codepoint == 0x300D or codepoint == 0x300F then -- closing quotes: 」 or 』
                -- Only call this for chapters that are already validated.
                if quote_depth == 1 then
                    line_buffer[#line_buffer + 1] = utf8.char(0x300D) -- 」
                else
                    line_buffer[#line_buffer + 1] = utf8.char(0x300F) -- 』
                end
                quote_depth = quote_depth - 1
            else
                line_buffer[#line_buffer + 1] = utf8.char(codepoint)
            end
        end
        output_lines[#output_lines + 1] = table.concat(line_buffer)
    end

    return output_lines
end

-- === Quote normalization & validation ===

local function flush_chapter_to_output(output_lines, current_chapter_title, current_chapter_lines)
    -- Helper: Flush accumulated chapter lines to output.
    -- Normalizes quote levels in chapters without unpaired quotes.
    if current_chapter_title == nil then
        return
    end

    local has_quote_issue = chapter_has_unpaired_quotes(current_chapter_lines)
    local final_lines = current_chapter_lines
    if not has_quote_issue then
        final_lines = normalize_quote_levels_in_lines(current_chapter_lines)
    end

    for _, line in ipairs(final_lines) do
        output_lines[#output_lines + 1] = line
    end
end

-- === Quote level normalization ===

local function normalize_quote_levels_in_ok_chapters(text)
    -- Process chapter-by-chapter. If a chapter has no pairing issue, normalize quote levels:
    -- outer -> 「」, inner -> 『』.
    local output_lines = {}
    local current_chapter_title = nil
    local current_chapter_lines = {}

    local lines = split_lines(text)
    for _, line in ipairs(lines) do
        if is_chapter_title(line) then
            flush_chapter_to_output(output_lines, current_chapter_title, current_chapter_lines)
            current_chapter_title = line
            current_chapter_lines = { line }
        else
            -- Group lines by chapter, normalizing quote levels for chapters without errors
            if current_chapter_title ~= nil then
                current_chapter_lines[#current_chapter_lines + 1] = line
            else
                output_lines[#output_lines + 1] = line
            end
        end
    end

    flush_chapter_to_output(output_lines, current_chapter_title, current_chapter_lines)

    return table.concat(output_lines, "\n")
end

-- === Paragraph validation data & helpers ===

local VALID_PARAGRAPH_ENDING_CODEPOINTS = {
    [0x21] = true,   -- !
    [0x2C] = true,   -- ,
    [0x2E] = true,   -- .
    [0x3F] = true,   -- ?
    [0x3A] = true,   -- :
    [0x7E] = true,   -- ~
    [0x2014] = true, -- —
    [0x2026] = true, -- …
    [0x3002] = true, -- 。
    [0x300B] = true, -- 》
    [0xFF01] = true, -- ！
    [0xFF0C] = true, -- ，
    [0xFF1A] = true, -- ：
    [0xFF1B] = true, -- ；
    [0xFF1F] = true, -- ？
    [0xFF5E] = true, -- ～
}

local CLOSING_QUOTE_CODEPOINTS = {
    [0x300D] = true, -- 」
    [0x300F] = true, -- 』
    [0x3011] = true, -- 】
    [0xFF09] = true, -- ）
}

-- Combine valid endings and closing quotes for invalid paragraph starts
local INVALID_PARAGRAPH_START_CODEPOINTS = {}
for cp, _ in pairs(VALID_PARAGRAPH_ENDING_CODEPOINTS) do
    INVALID_PARAGRAPH_START_CODEPOINTS[cp] = true
end
for cp, _ in pairs(CLOSING_QUOTE_CODEPOINTS) do
    INVALID_PARAGRAPH_START_CODEPOINTS[cp] = true
end

-- === Paragraph punctuation validation helpers ===

local function check_paragraph_ending(codepoints, line_number, validation_issues)
    -- Helper: Check if paragraph ends with valid punctuation (skipping trailing quotes).
    if #codepoints == 0 then
        return
    end

    local last_valid_idx = #codepoints
    while last_valid_idx > 0 and CLOSING_QUOTE_CODEPOINTS[codepoints[last_valid_idx]] do
        last_valid_idx = last_valid_idx - 1
    end

    if last_valid_idx > 0 then
        local final_cp = codepoints[last_valid_idx]
        if not VALID_PARAGRAPH_ENDING_CODEPOINTS[final_cp] then
            validation_issues[#validation_issues + 1] = {
                line_no = line_number,
                kind = "invalid_ending",
                note = "paragraph ends with invalid punctuation"
            }
        end
    end
end

local function check_paragraph_start(codepoints, line_number, validation_issues)
    -- Helper: Check if paragraph starts with invalid punctuation.
    if #codepoints == 0 then
        return
    end

    local first_cp = codepoints[1]
    if INVALID_PARAGRAPH_START_CODEPOINTS[first_cp] then
        validation_issues[#validation_issues + 1] = {
            line_no = line_number,
            kind = "invalid_start",
            note = "paragraph starts with invalid punctuation"
        }
    end
end

local function is_dash_only_line(line)
    -- Check if line contains EXACTLY 6 dash characters (the valid separator count).
    -- First remove paragraph indentation, then check.
    local trimmed = trim_ends(line)
    -- Remove the paragraph indent prefix (　　)
    local indent_end_pos = consume_indent_prefix(trimmed, 1)
    local content_start_pos = indent_end_pos

    -- Get all codepoints from the remaining content
    local dash_count = 0
    for byte_pos, cp in utf8.codes(trimmed) do
        if byte_pos >= content_start_pos then
            if cp == 0x2D then -- 0x2D is dash '-'
                dash_count = dash_count + 1
            else
                return false -- Found non-dash character
            end
        end
    end

    return dash_count == 6
end

local function check_paragraph_punctuation(text)
    -- Check that paragraphs:
    -- 1. End with valid punctuation: ， 。 ？ ！ … , . ? !
    -- 2. If ends with 』 」 ）, strip them and check what's underneath - must follow rule 1
    -- 3. If second-to-last is still 』 」 ）, keep stripping and check what's underneath
    -- 4. Don't start with ， 。 ？ ！ 」 』 … or , . ? !
    -- Returns: table of issues

    local validation_issues = {}
    local lines = split_lines(text)
    for line_number, line in ipairs(lines) do
        -- Skip empty lines, chapter titles, separator lines, and dash-only lines
        if line:match("%S") and not is_chapter_title(line) and not is_separator(line) and not is_dash_only_line(line) then
            local trimmed = trim_ends(line)

            if #trimmed > 0 then
                -- Collect all codepoints for easier access
                local codepoints = {}
                for _, codepoint in utf8.codes(trimmed) do
                    codepoints[#codepoints + 1] = codepoint
                end

                check_paragraph_ending(codepoints, line_number, validation_issues)
                check_paragraph_start(codepoints, line_number, validation_issues)
            end
        end
    end

    return validation_issues
end

local function log_path_for_output(output_path)
    -- Generate log file path in same directory as output file.
    -- Falls back to 'log' in current directory if no path separator found.
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
    local quote_stack = {}
    for _, item in ipairs(chapter_line_items) do
        local line_number = item.line_no
        local line_text = item.text
        for _, codepoint in utf8.codes(line_text) do
            if codepoint == 0x300C or codepoint == 0x300E then     -- opening quotes: 「 or 『
                quote_stack[#quote_stack + 1] = { codepoint = codepoint, line_no = line_number }
            elseif codepoint == 0x300D or codepoint == 0x300F then -- closing quotes: 」 or 』
                local opening_quote_info = quote_stack[#quote_stack]
                quote_stack[#quote_stack] = nil
                if opening_quote_info == nil then
                    return { kind = "extra_close", line_no = line_number, note = "closing quote without opener" }
                end

                if codepoint == 0x300D and opening_quote_info.codepoint ~= 0x300C then -- 」 but expected 「
                    return { kind = "mismatch", line_no = line_number, note = "expected 『 but found 」" }
                end

                if codepoint == 0x300F and opening_quote_info.codepoint ~= 0x300E then -- 』 but expected 『
                    return { kind = "mismatch", line_no = line_number, note = "expected 「 but found 』" }
                end
            end
        end
    end

    if #quote_stack ~= 0 then
        -- Report the line number of the last unmatched opening quote (the one still on the stack).
        local last_unclosed = quote_stack[#quote_stack]
        local opening_line_no = last_unclosed and last_unclosed.line_no or 0

        return { kind = "unclosed", line_no = opening_line_no, note = "unclosed opening quote(s) by end of chapter" }
    end

    return nil
end

-- === Quote issue logging helpers ===

local function collect_chapter_items(chapter_title, chapter_title_line_no)
    -- Helper: Return initial chapter item list (with title).
    return { { line_no = chapter_title_line_no, text = chapter_title } }
end

local function check_chapter_for_issues(chapter_items)
    -- Helper: Check if chapter has quote issues, return issue or nil.
    local quote_issue = first_quote_issue_in_chapter(chapter_items)
    return quote_issue
end

local function format_quote_issue_item(title, title_line_no, issue)
    -- Helper: Format a single quote issue for the log.
    local chapter_line = string.format("- Chapter at line %d: %s", title_line_no, title)
    local issue_line = string.format(
        "  First issue at line %d (%s): %s",
        issue.line_no,
        issue.kind,
        issue.note
    )
    return chapter_line, issue_line
end

local function write_unpaired_quote_log(text, output_path)
    -- Split output into chapters, validate quotes per chapter, and include output line numbers.
    -- Detects all quote issues per chapter and writes to log file.

    -- Scan text line-by-line, grouping by chapter
    local current_chapter_title = nil
    local current_chapter_title_line_no = 0
    local current_chapter_items = {}
    local quote_issues = {}

    local lines = split_lines(text)
    for line_number, line in ipairs(lines) do
        if is_chapter_title(line) then
            -- End previous chapter and check for issues
            if current_chapter_title ~= nil then
                local quote_issue = check_chapter_for_issues(current_chapter_items)
                if quote_issue ~= nil then
                    quote_issues[#quote_issues + 1] = {
                        title = current_chapter_title,
                        title_line_no = current_chapter_title_line_no,
                        issue = quote_issue,
                    }
                end
            end
            -- Start new chapter
            current_chapter_title = line
            current_chapter_title_line_no = line_number
            current_chapter_items = collect_chapter_items(line, line_number)
        else
            -- Add line to current chapter
            if current_chapter_title ~= nil then
                current_chapter_items[#current_chapter_items + 1] = { line_no = line_number, text = line }
            end
        end
    end

    -- Don't forget final chapter
    if current_chapter_title ~= nil then
        local quote_issue = check_chapter_for_issues(current_chapter_items)
        if quote_issue ~= nil then
            quote_issues[#quote_issues + 1] = {
                title = current_chapter_title,
                title_line_no = current_chapter_title_line_no,
                issue = quote_issue,
            }
        end
    end

    -- Format and write log file
    local log_file_path = log_path_for_output(output_path)
    delete_file_if_exists(log_file_path)

    local log_lines = {}
    if #quote_issues > 0 then
        log_lines[#log_lines + 1] = "Unpaired/mismatched quotes detected (line numbers are in the output file):"
        for _, issue_item in ipairs(quote_issues) do
            local chapter_line, issue_line = format_quote_issue_item(
                issue_item.title,
                issue_item.title_line_no,
                issue_item.issue
            )
            log_lines[#log_lines + 1] = chapter_line
            log_lines[#log_lines + 1] = issue_line
        end
    end

    write_all(log_file_path, table.concat(log_lines, "\n"))

    -- Notify user if issues were found
    if #log_lines > 0 then
        io.stderr:write("Quote issues detected; see log at: " .. tostring(log_file_path) .. "\n")
    end
end

-- === Paragraph validation logging helpers ===

local function append_paragraph_issues_to_log(log_lines, paragraph_issues)
    -- Helper: Append paragraph punctuation issues to log lines.
    if #paragraph_issues == 0 then
        return
    end

    log_lines[#log_lines + 1] = "Paragraph punctuation issues detected (line numbers are in the output file):"
    for _, issue in ipairs(paragraph_issues) do
        log_lines[#log_lines + 1] = string.format("- Line %d (%s): %s", issue.line_no, issue.kind, issue.note)
    end
end

local function prepend_existing_log_if_present(log_lines, log_file_path)
    -- Helper: Prepend existing log content if file exists.
    if not file_exists(log_file_path) then
        return
    end

    local existing_log = read_all(log_file_path)
    if #existing_log > 0 then
        log_lines[#log_lines + 1] = existing_log
        log_lines[#log_lines + 1] = ""
    end
end

local function write_paragraph_check_log(text, output_path)
    -- Check paragraphs for punctuation issues and write to log if found.
    local paragraph_issues = check_paragraph_punctuation(text)
    local log_file_path = log_path_for_output(output_path)

    local log_lines = {}
    prepend_existing_log_if_present(log_lines, log_file_path)
    append_paragraph_issues_to_log(log_lines, paragraph_issues)

    if #log_lines > 0 then
        write_all(log_file_path, table.concat(log_lines, "\n"))
        io.stderr:write("Paragraph issues detected; see log at: " .. tostring(log_file_path) .. "\n")
    end
end

-- === CLI ===

local function parse_args(argv)
    -- Parse command-line arguments. Returns table with 'help' or 'input' field.
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
    -- Generate backup file path: 'original_<basename>.txt' in same directory as input.
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

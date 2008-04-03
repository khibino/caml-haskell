main = getArgs >>= putStr . flip id "\n" . foldr (.) id . map (showHex . read)

#!/usr/bin/env bash

set -u

validate_spaces () {
    local issues_found=0
    while IFS= read -r -d '' file; do
        # Check for trailing whitespace and print line number if found
        while IFS=: read -r line_num line; do
            echo "Trailing whitespace found in $file at line $line_num: $line"
            issues_found=1
        done < <(grep -n "[[:blank:]]$" "$file")

        # Check if the last line ends with a new line
        if [ -s "$file" ] && [ "$(tail -c 1 "$file" | od -An -t x1 | tr -d '[:space:]')" != "0a" ]; then
            echo "Last line does not end with a new line in: $file"
            issues_found=1
        fi
    done < <(find ArkLib -type f -name '*.lean' -print0)

    if [ "$issues_found" -ne 0 ]; then
        echo "Run \`bash ./scripts/lintWhitespace.sh -i\` to fix whitespace issues."
    fi

    return "$issues_found"
}

fix_spaces_inplace() {
    while IFS= read -r -d '' file; do
        # Perl's in-place mode has the same syntax on GNU/Linux and macOS.
        perl -0777 -pi -e 's/[ \t]+(?=\n)//g; s/[ \t]+\z//; s/\z/\n/ unless /\n\z/' "$file"
    done < <(find ArkLib -type f -name '*.lean' -print0)
}

is_inplace=0

while getopts ":i" option; do
  case $option in
    i)
      is_inplace=1 ;;
    *)
      echo "Usage: $0 [-i]"
      exit 1
      ;;
  esac
done

if [ "$is_inplace" -eq 1 ]; then
    fix_spaces_inplace
else
    validate_spaces
fi


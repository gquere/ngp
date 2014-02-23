ngp
===

"ncurses grep" empowers developpers by saving time and providing a convenient and fully functional search tool.
It lets you browse results in a Vim-like style and open them in your favourite editor at the right line.


Features:
- search for a pattern/a regexp in a folder or a file
- by default, only source files are scanned, though a raw mode or special extensions may be specified
- follow/no-follow symlinks, exclude directories, ignore case
- and of course perform subsearches in your search !

Usage:
- use arrows and page up/down to navigate the results
- hit enter to open a result
- hit / to perform a subsearch (regexp, patterns count as regexps - no worries)
- hit q or to quit the current search


Installation
------------

- ./configure
- make
- make install
- enjoy !

Looking for "boot_param" pattern in kernel

![Looking for "boot_param" pattern] (/search.png)


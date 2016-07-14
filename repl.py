"""
Run the interpreter from the command line.
"""

import sys
import pythological, parser

def main(argv):
    #defs = sum(map(load, argv[1:]), ())
    program = load(argv[1])
    repl(program)

def repl(program):
    while True:
        line = raw_input('> ')
        if line == 'quit': break
        try:
            program.q(line)
        except parser.Unparsable as e:
            syntax_error(e, 'stdin')

def load(filename):
    with open(filename) as f:
        text = f.read()
    try:
        return parser.parse(text)
    except parser.Unparsable as e:
        syntax_error(e, filename)
        sys.exit(1)

def syntax_error(e, filename):
    line_no, prefix, suffix = where(e)
    prefix, suffix = sanitize(prefix), sanitize(suffix)
    sys.stderr.write("%s:%d:%d: Syntax error\n" % (filename, line_no, len(prefix)))
    sys.stderr.write('  ' + prefix + suffix + '\n')
    sys.stderr.write('  ' + ' '*len(prefix) + '^\n')

def where(e):
    before, after = e.failure
    line_no = before.count('\n')
    prefix = (before+'\n').splitlines()[line_no]
    suffix = (after+'\n').splitlines()[0] # XXX what if right on newline?
    return line_no+1, prefix, suffix

def sanitize(s):
    "Make s predictably printable, sans control characters like tab."
    return ''.join(c if ' ' <= c < chr(127) else ' ' # XXX crude
                   for c in s)

if __name__ == '__main__':
    main(sys.argv)

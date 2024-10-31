import { CommonTokenStream, CharStream, FileStream } from 'antlr4';
import StellaLexer from './stella/stellaLexer';
import StellaParser from './stella/stellaParser';
import { AstTransformer } from './visitors';
import { typecheckProgram } from './typechecker';
import { PrettyPrinter } from './pretty-printer';

let inputStream: CharStream;

if (process.argv.length === 2) {
  // @ts-expect-error The typings of ANTLR are not perfect
  inputStream = new FileStream(process.stdin.fd);
} else if (process.argv.length === 3) {
  inputStream = new FileStream(process.argv[2]);
} else {
  throw 'Usage: node index.js [path/to/file.stella]';
}

const lexer = new StellaLexer(inputStream);
const tokenStream = new CommonTokenStream(lexer);
const parser = new StellaParser(tokenStream);

// The entry point for parsing is a "program"
const program = parser.program();

const t = new AstTransformer();
const ast = t.visitProgram(program);
// console.log(JSON.stringify(ast, (k, v) => v ?? null, 4));
typecheckProgram(ast);
// console.log(new PrettyPrinter().visitProgram(program));

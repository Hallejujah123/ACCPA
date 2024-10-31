// @ts-check
const { execSync } = require('node:child_process');
const { openSync, writeSync, readFileSync } = require('node:fs');

const output = execSync(
  'antlr4 -v 4.12.0 -visitor -Dlanguage=TypeScript *.g4',
  {
    cwd: './src/stella/',
  }
).toString();

if (output !== '') {
  console.log('An error occurred generating the parser:');
  console.error(output);
  process.exit(1);
}

const preamble = Buffer.from('// @ts-nocheck\n');

const lexerFd = openSync('./src/stella/stellaLexer.ts', 'r+');
const lexerData = readFileSync(lexerFd);
writeSync(lexerFd, preamble, 0, preamble.length, 0);
writeSync(lexerFd, lexerData, 0, lexerData.length, preamble.length);

const parserFd = openSync('./src/stella/stellaParser.ts', 'r+');
const parserData = readFileSync(parserFd);
writeSync(parserFd, preamble, 0, preamble.length, 0);
writeSync(parserFd, parserData, 0, parserData.length, preamble.length);

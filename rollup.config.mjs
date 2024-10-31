import typescript from '@rollup/plugin-typescript';
import { nodeResolve } from '@rollup/plugin-node-resolve';

/** @type {import('rollup').RollupOptions} */
export default {
  input: './src/index.ts',
  output: {
    file: './build/index.js',
    format: 'cjs',
  },
  plugins: [nodeResolve(), typescript()],
};

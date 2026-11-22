// Tiny stack VM for make.fun's tiny ISA: bounds, then trap order, then each opcode (ISA.md, vm.mjs).

import { readFileSync, writeFileSync, mkdirSync, readdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256, CALLS_MAX = 64, MEMORY_WORDS = 256, STEP_LIMIT = 1_000_000, OUTPUT_MAX = 65_536;
const DIV_ZERO = 4, BAD_OPCODE = 5, MEMORY = 6, CALL_DEPTH = 7, RET_EMPTY = 8, PC = 9, STEPS = 10, OUTPUT = 11;

const IMM = new Map<number, number>([[0x01, 1], [0x02, 4], [0x30, 2], [0x31, 2], [0x32, 2], [0x33, 2]]);
const POP = new Map<number, number>([
  [0x03, 1], [0x04, 1], [0x05, 2], [0x06, 2], [0x07, 3],
  [0x10, 2], [0x11, 2], [0x12, 2], [0x13, 2], [0x14, 2], [0x15, 2], [0x16, 2], [0x17, 1],
  [0x18, 2], [0x19, 2], [0x1a, 2], [0x1b, 1], [0x1c, 2], [0x1d, 2], [0x1e, 2],
  [0x20, 2], [0x21, 2], [0x22, 2], [0x31, 1], [0x32, 1], [0x40, 1], [0x41, 2], [0x50, 1], [0x51, 1], [0x53, 1],
]);
const PUSH = new Map<number, number>([
  [0x01, 1], [0x02, 1], [0x04, 2], [0x05, 2], [0x06, 3], [0x07, 3],
  [0x10, 1], [0x11, 1], [0x12, 1], [0x13, 1], [0x14, 1], [0x15, 1], [0x16, 1], [0x17, 1],
  [0x18, 1], [0x19, 1], [0x1a, 1], [0x1b, 1], [0x1c, 1], [0x1d, 1], [0x1e, 1],
  [0x20, 1], [0x21, 1], [0x22, 1], [0x40, 1], [0x52, 1],
]);

interface Answer { stdout: Buffer; exit: number }

/** One program to its end: the bytes it wrote and the code it ended with. */
function run(program: Buffer, input: Buffer): Answer {
  const n = program.length;
  const stack = new Int32Array(STACK_MAX), calls = new Int32Array(CALLS_MAX), memory = new Int32Array(MEMORY_WORDS);
  const out = Buffer.alloc(OUTPUT_MAX);
  let sp = 0, csp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  const done = (exit: number): Answer => ({ stdout: out.subarray(0, olen), exit });

  for (;;) {
    if (steps === STEP_LIMIT) return done(STEPS);
    if (pc < 0 || pc >= n) return done(PC);
    const op = program[pc]!;
    const imm = IMM.get(op), pops = POP.get(op), pushes = PUSH.get(op);
    if (imm === undefined && pops === undefined && pushes === undefined && op !== 0x00 && op !== 0x34) return done(BAD_OPCODE);
    const immediate = imm ?? 0;
    if (pc + immediate >= n) return done(PC);
    steps++;
    const next = pc + 1 + immediate;
    const npop = pops ?? 0, npush = pushes ?? 0;
    if (sp < npop) return done(2);
    if (sp - npop + npush > STACK_MAX) return done(3);
    pc = next;

    switch (op) {
      case 0x00: return done(0);
      case 0x01: stack[sp++] = (program[next - 1]! << 24) >> 24; break;
      case 0x02: stack[sp++] = program[next - 4]! | (program[next - 3]! << 8) | (program[next - 2]! << 16) | (program[next - 1]! << 24); break;
      case 0x03: sp--; break;
      case 0x04: stack[sp] = stack[sp - 1]!; sp++; break;
      case 0x05: { const t = stack[sp - 1]!; stack[sp - 1] = stack[sp - 2]!; stack[sp - 2] = t; break; }
      case 0x06: stack[sp] = stack[sp - 2]!; sp++; break;
      case 0x07: { const a = stack[sp - 3]!; stack[sp - 3] = stack[sp - 2]!; stack[sp - 2] = stack[sp - 1]!; stack[sp - 1] = a; break; }
      case 0x17: stack[sp - 1] = -stack[sp - 1]! | 0; break;
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]!; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1]!, a = stack[sp - 2]!;
        let r = 0;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: if (b === 0) return done(DIV_ZERO); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: if (b === 0) return done(DIV_ZERO); r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: if (b === 0) return done(DIV_ZERO); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: if (b === 0) return done(DIV_ZERO); r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2; stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next - 2]! | (program[next - 1]! << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = stack[--sp]!; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALLS_MAX) return done(CALL_DEPTH);
        calls[csp++] = next;
        pc = program[next - 2]! | (program[next - 1]! << 8);
        break;
      case 0x34:
        if (csp === 0) return done(RET_EMPTY);
        pc = calls[--csp]!;
        break;
      case 0x40: {
        const addr = stack[sp - 1]!;
        if (addr < 0 || addr >= MEMORY_WORDS) return done(MEMORY);
        stack[sp - 1] = memory[addr]!;
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1]!, v = stack[sp - 2]!;
        if (addr < 0 || addr >= MEMORY_WORDS) return done(MEMORY);
        sp -= 2; memory[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = Buffer.from(String(stack[sp - 1]!), 'utf8');
        if (olen + bytes.length > OUTPUT_MAX) return done(OUTPUT);
        sp--; bytes.copy(out, olen); olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUTPUT_MAX) return done(OUTPUT);
        out[olen++] = stack[--sp]! & 255;
        break;
      case 0x52: stack[sp++] = inPos < input.length ? input[inPos++]! : -1; break;
      case 0x53: return done(stack[--sp]! & 255);
      default: return done(BAD_OPCODE);
    }
  }
}

/** Every instance directory under the input root, sorted, so two runs answer in the same order. */
function instanceIds(root: string): string[] {
  return readdirSync(root, { withFileTypes: true }).filter((d) => d.isDirectory()).map((d) => d.name).sort();
}

const inputRoot = process.env.TINY_INPUT ?? '/input';
const outputRoot = process.env.TINY_OUTPUT ?? '/output';
mkdirSync(outputRoot, { recursive: true });

for (const id of instanceIds(inputRoot)) {
  const dir = join(inputRoot, id);
  const program = readFileSync(join(dir, 'program.bin'));
  const input = existsSync(join(dir, 'input.bin')) ? readFileSync(join(dir, 'input.bin')) : Buffer.alloc(0);
  const answer = run(program, input);
  const outDir = join(outputRoot, id);
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, 'stdout.bin'), answer.stdout);
  writeFileSync(join(outDir, 'exit.txt'), `${answer.exit}`);
}

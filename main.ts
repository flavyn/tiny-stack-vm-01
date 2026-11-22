// Tiny stack VM: port of the kit's vm.mjs, behaviour for behaviour.
// Answers every instance under /input, writes /output/<id>/stdout.bin + exit.txt.
import { readFileSync, readdirSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const enc = new TextEncoder();
const STACK_MAX = 256, CALLS_MAX = 64, STEP_LIMIT = 1000000, OUTPUT_MAX = 65536, MEM_WORDS = 256;

// Opcode byte -> [immediate bytes, pops, pushes]. 0x1f is not an opcode.
const OP = new Map();
const def = (b, imm, pops, pushes) => OP.set(b, [imm, pops, pushes]);
for (let b = 0x10; b <= 0x22; b++) if (b !== 0x1f) def(b, 0, 2, 1);
def(0x17, 0, 1, 1); def(0x1b, 0, 1, 1);
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1);
def(0x03, 0, 1, 0); def(0x04, 0, 1, 2); def(0x05, 0, 2, 2);
def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0);
def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

export function run(program, input) {
  const n = program.length;
  const D = new Int32Array(STACK_MAX); let sp = 0;
  const C = new Int32Array(CALLS_MAX); let csp = 0;
  const M = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUTPUT_MAX); let olen = 0;
  let inPos = 0, pc = 0, steps = 0;
  const done = (exit, trap) => ({ stdout: out.slice(0, olen), exit, trap, steps });
  const trap = (code) => done(code, code);

  for (;;) {
    // Trap checks run before the opcode's effect; output written so far is kept.
    if (steps === STEP_LIMIT) return trap(10);
    if (pc < 0 || pc >= n) return trap(9);
    const op = program[pc], m = OP.get(op);
    if (m === undefined) return trap(5);
    const [imm, pops, pushes] = m;
    if (pc + imm >= n) return trap(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return trap(2);
    if (sp - pops + pushes > STACK_MAX) return trap(3);
    pc = next;

    // All binary ops: b on top, a below. The reference writes r back as int32.
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = D[sp - 1], a = D[sp - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return trap(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 0x14) { if (b === 0) return trap(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 0x15) { if (b === 0) return trap(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (b === 0) return trap(4); r = (a >>> 0) % (b >>> 0) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2; D[sp++] = r;
      continue;
    }

    switch (op) {
      case 0x00: return done(0, null);
      case 0x01: D[sp++] = (program[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = program[next - 4] | (program[next - 3] << 8) | (program[next - 2] << 16) | (program[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const t = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = t; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next - 2] | (program[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALLS_MAX) return trap(7);
        C[csp++] = next;
        pc = program[next - 2] | (program[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return trap(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return trap(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= MEM_WORDS) return trap(6);
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > OUTPUT_MAX) return trap(11);
        sp--; out.set(bytes, olen); olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUTPUT_MAX) return trap(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: return done(D[--sp] & 255, null);
    }
  }
}

function main() {
  const ids = readdirSync('/input').filter((s) => /^i\d{3}$/.test(s)).sort();
  for (const id of ids) {
    const program = readFileSync(join('/input', id, 'program.bin'));
    const input = readFileSync(join('/input', id, 'input.bin'));
    const r = run(program, input);
    const dir = join('/output', id);
    mkdirSync(dir, { recursive: true });
    writeFileSync(join(dir, 'stdout.bin'), r.stdout);
    writeFileSync(join(dir, 'exit.txt'), String(r.exit) + '\n');
  }
}
main();

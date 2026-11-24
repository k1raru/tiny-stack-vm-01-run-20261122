import { readdirSync, readFileSync, mkdirSync, writeFileSync } from 'node:fs';

// Tiny stack VM for make.fun's 32-bit stack ISA: wrapping arithmetic, a
// 256-value data stack, a 64-deep call stack, 256 words of memory, input
// and output, and ten traps with their own exit codes. One run answers
// every program in /input/<id>/, writing /output/<id>/stdout.bin and
// /output/<id>/exit.txt. No network, no clock, no environment: the same
// input always gives the same output.

// Opcode table: [byte, immediate bytes, pops, pushes].
const OPS = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const IM = new Int8Array(256).fill(-1);
const PO = new Int8Array(256);
const PU = new Int8Array(256);
for (const [b, i, p, q] of OPS) { IM[b] = i; PO[b] = p; PU[b] = q; }

// Runs one program on its input bytes; returns the bytes it wrote and its
// exit code (a trap's code included).
function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (e) => ({ o: out.subarray(0, ol), e });
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const im = IM[op];
    if (im < 0) return end(5);
    if (pc + im >= n) return end(9);
    st++;
    const nx = pc + 1 + im;
    if (sp < PO[op]) return end(2);
    if (sp - PO[op] + PU[op] > 256) return end(3);
    pc = nx;
    switch (op) {
      case 0: return end(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19:
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20:
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21:
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22:
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) {
          const v = D[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 65: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr > 255) return end(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 80: {
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      default: return end(D[--sp] & 255);
    }
  }
}

for (const id of readdirSync('/input').sort()) {
  if (id[0] === '.') continue;
  let prog;
  try { prog = readFileSync('/input/' + id + '/program.bin'); } catch { continue; }
  let inp = new Uint8Array(0);
  try { inp = readFileSync('/input/' + id + '/input.bin'); } catch {}
  const r = run(prog, inp);
  mkdirSync('/output/' + id, { recursive: true });
  writeFileSync('/output/' + id + '/stdout.bin', r.o);
  writeFileSync('/output/' + id + '/exit.txt', String(r.e));
}

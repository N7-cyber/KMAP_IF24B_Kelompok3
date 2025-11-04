/* =============================================================================
   BOOLEAN ALGEBRA & KARNAUGH MAP SIMULATOR
   Kelompok Pusay - Rangkaian Digital
   
   DESKRIPSI:
   Aplikasi web interaktif untuk evaluasi ekspresi Boolean, generate tabel
   kebenaran, visualisasi K-Map dengan Gray code, dan minimasi menggunakan
   algoritma Quine-McCluskey.
   
   STRUKTUR KODE:
   1. Constants & Utilities (Gray Code, Helper Functions)
   2. Tokenizer & Parser (Shunting-Yard Algorithm)
   3. RPN Evaluator
   4. Quine-McCluskey Algorithm (SOP & POS)
   5. K-Map Layout & Rendering
   6. Truth Table Generation
   7. Application State Management
   8. Event Handlers & UI Updates
   9. Statistics Tracking
   10. Image Export Functionality
   
   ALGORITMA UTAMA:
   - Shunting-Yard: Konversi infix → RPN (O(n))
   - Quine-McCluskey: Minimasi Boolean (O(3^n × n²))
   - Gray Code: Ordering optimal untuk K-Map adjacency
   
============================================================================= */

'use strict';

/* =============================================================================
   1. CONSTANTS & UTILITIES
============================================================================= */
const GRAY2 = [0, 1];                    // 2-bit Gray: 00, 01
const GRAY4 = [0, 1, 3, 2];              // 4-bit Gray: 00, 01, 11, 10
const MAX_VARS = 4;                       // K-Map maximum variables
const MAX_TRUTH_TABLE_VARS = 8;           // Truth table maximum

// DOM Element Cache
const $ = id => document.getElementById(id);
const toBin = (n, width) => n.toString(2).padStart(width, '0');

/**
 * Extract and sort unique variables from expression
 * @param {Array} vars - Array of variable characters
 * @returns {Array} Sorted unique variables
 */
function uniqueSortedVars(vars) {
  const set = new Set(vars.map(v => v.toUpperCase()));
  return Array.from(set).sort();
}

/**
 * Extract all variables from expression string
 * @param {string} expr - Boolean expression
 * @returns {Array} Array of unique sorted variables
 */
function extractVars(expr) {
  const vars = (expr.match(/[A-Za-z]/g) || []).map(ch => ch.toUpperCase());
  return uniqueSortedVars(vars);
}

/* =============================================================================
   2. TOKENIZER (Lexical Analysis)
   Converts expression string into tokens
============================================================================= */
function tokenize(raw) {
  const src = raw.replace(/\s+/g, '');    // Remove whitespace
  const tokens = [];
  let i = 0;

  while (i < src.length) {
    const ch = src[i];

    // Number literals (0 or 1)
    if (ch === '0' || ch === '1') {
      tokens.push({ type: 'NUM', value: Number(ch) });
      i++;
      continue;
    }

    // Variables (A-Z, case insensitive)
    if (/[A-Za-z]/.test(ch)) {
      const v = ch.toUpperCase();
      tokens.push({ type: 'VAR', value: v });
      i++;
      
      // Postfix NOT (') - dapat berulang (A'', A''')
      let negCount = 0;
      while (src[i] === "'") {
        negCount++;
        i++;
      }
      // Odd number of ' means NOT
      if (negCount % 2 === 1) {
        tokens.push({
          type: 'OP',
          value: 'NOT',
          unary: true,
          postfix: true,
          precedence: 4,
          associativity: 'right'
        });
      }
      continue;
    }

    // Parentheses
    if (ch === '(') {
      tokens.push({ type: 'LP' });
      i++;
      continue;
    }
    if (ch === ')') {
      tokens.push({ type: 'RP' });
      i++;
      continue;
    }

    // Prefix NOT operators (!, ~)
    if (ch === '!' || ch === '~') {
      tokens.push({
        type: 'OP',
        value: 'NOT',
        unary: true,
        precedence: 4,
        associativity: 'right'
      });
      i++;
      continue;
    }

    // Binary operators
    if ('&*+|^'.includes(ch)) {
      let op;
      if (ch === '&' || ch === '*') op = 'AND';
      else if (ch === '+' || ch === '|') op = 'OR';
      else if (ch === '^') op = 'XOR';
      
      // Precedence: OR(1) < XOR(2) < AND(3) < NOT(4)
      const prec = op === 'OR' ? 1 : (op === 'XOR' ? 2 : 3);
      
      tokens.push({
        type: 'OP',
        value: op,
        precedence: prec,
        associativity: 'left'
      });
      i++;
      continue;
    }

    throw new Error(`Karakter tidak dikenali pada posisi ${i}: '${ch}'`);
  }
  return tokens;
}

/* =============================================================================
   3. PARSER (Shunting-Yard Algorithm)
   Converts infix notation to RPN (Reverse Polish Notation)
============================================================================= */

/**
 * Check if token represents an operand
 */
function isOperand(tok) {
  return tok && (
    tok.type === 'VAR' || 
    tok.type === 'NUM' || 
    tok.type === 'RP' || 
    (tok.type === 'OP' && tok.postfix)
  );
}

/**
 * Check if token can begin an operand/expression
 */
function beginsOperand(tok) {
  return tok && (
    tok.type === 'VAR' || 
    tok.type === 'NUM' || 
    tok.type === 'LP' || 
    (tok.type === 'OP' && tok.value === 'NOT' && !tok.postfix)
  );
}

/**
 * Convert infix tokens to RPN using Shunting-Yard algorithm
 * Supports implicit AND between adjacent operands
 * @param {Array} tokens - Array of tokens from tokenizer
 * @returns {Array} Tokens in RPN order
 */
function toRPN(tokens) {
  const output = [];
  const stack = [];
  const withImplicit = [];
  
  // Phase 1: Insert implicit AND operators
  for (let i = 0; i < tokens.length; i++) {
    withImplicit.push(tokens[i]);
    const a = tokens[i];
    const b = tokens[i + 1];
    
    // Insert implicit AND between: )( , )VAR , VAR( , VARVAR , NUMVAR , etc.
    if (isOperand(a) && beginsOperand(b)) {
      withImplicit.push({
        type: 'OP',
        value: 'AND',
        precedence: 3,
        associativity: 'left',
        implicit: true
      });
    }
  }

  // Phase 2: Shunting-Yard algorithm
  for (let i = 0; i < withImplicit.length; i++) {
    const t = withImplicit[i];
    
    // Operands go directly to output
    if (t.type === 'VAR' || t.type === 'NUM') {
      output.push(t);
      continue;
    }
    
    // Postfix NOT
    if (t.type === 'OP' && t.postfix && t.value === 'NOT') {
      output.push(t);
      continue;
    }
    
    // Prefix unary operators
    if (t.type === 'OP' && t.unary && !t.postfix) {
      stack.push(t);
      continue;
    }
    
    // Binary operators
    if (t.type === 'OP' && !t.unary) {
      while (stack.length) {
        const top = stack[stack.length - 1];
        if (
          top.type === 'OP' && (
            (top.precedence > t.precedence) ||
            (top.precedence === t.precedence && t.associativity === 'left')
          )
        ) {
          output.push(stack.pop());
        } else {
          break;
        }
      }
      stack.push(t);
      continue;
    }
    
    // Left parenthesis
    if (t.type === 'LP') {
      stack.push(t);
      continue;
    }
    
    // Right parenthesis
    if (t.type === 'RP') {
      while (stack.length && stack[stack.length - 1].type !== 'LP') {
        output.push(stack.pop());
      }
      if (!stack.length) {
        throw new Error(`Kurung buka '(' tidak memiliki pasangan kurung tutup ')'`);
      }
      stack.pop(); // Remove LP
      continue;
    }
  }
  
  // Empty remaining stack
  while (stack.length) {
    const s = stack.pop();
    if (s.type === 'LP' || s.type === 'RP') {
      throw new Error(`Kurung tidak seimbang - ada kurung yang tidak tertutup dengan benar`);
    }
    output.push(s);
  }
  
  return output;
}

/* =============================================================================
   4. RPN EVALUATOR
   Evaluates RPN expression with given variable environment
============================================================================= */
/**
 * Evaluate RPN expression
 * @param {Array} rpn - Tokens in RPN order
 * @param {Object} env - Variable values {A: 0, B: 1, ...}
 * @returns {number} Result (0 or 1)
 */
function evalRPN(rpn, env) {
  const stack = [];
  
  for (const token of rpn) {
    if (token.type === 'NUM') {
      stack.push(!!token.value);
    } 
    else if (token.type === 'VAR') {
      if (!(token.value in env)) {
        throw new Error(`Variabel ${token.value} tidak didefinisikan dalam environment`);
      }
      stack.push(!!env[token.value]);
    } 
    else if (token.type === 'OP') {
      if (token.value === 'NOT') {
        if (stack.length < 1) {
          throw new Error("Operator NOT membutuhkan 1 operand");
        }
        const a = stack.pop();
        stack.push(!a);
      } else {
        if (stack.length < 2) {
          throw new Error(`Operator ${token.value} membutuhkan 2 operand`);
        }
        const b = stack.pop();
        const a = stack.pop();
        
        if (token.value === 'AND') {
          stack.push(a && b);
        } else if (token.value === 'OR') {
          stack.push(a || b);
        } else if (token.value === 'XOR') {
          stack.push(Boolean(a) !== Boolean(b));
        } else {
          throw new Error(`Operator tidak dikenal: ${token.value}`);
        }
      }
    }
  }
  
  if (stack.length !== 1) {
    throw new Error("Ekspresi tidak valid - periksa sintaks dengan teliti");
  }
  
  return stack[0] ? 1 : 0;
}

/* =============================================================================
   5. QUINE-MCCLUSKEY ALGORITHM
   Boolean function minimization algorithm
============================================================================= */

/**
 * Count number of 1's in binary string
 */
function countOnes(binStr) {
  return binStr.split('').filter(c => c === '1').length;
}

/**
 * Check if two binary strings differ by exactly 1 bit
 */
function canCombine(a, b) {
  let diff = 0;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) diff++;
    if (diff > 1) return false;
  }
  return diff === 1;
}

/**
 * Combine two binary strings (differing bit becomes '-')
 */
function combine(a, b) {
  let result = '';
  for (let i = 0; i < a.length; i++) {
    result += (a[i] === b[i]) ? a[i] : '-';
  }
  return result;
}

/**
 * Check if implicant covers a minterm
 */
function covers(implicant, mintermBin) {
  for (let i = 0; i < implicant.length; i++) {
    if (implicant[i] === '-') continue;
    if (implicant[i] !== mintermBin[i]) return false;
  }
  return true;
}

/**
 * Main Quine-McCluskey minimization algorithm
 * @param {Array} minterms - Array of minterm indices
 * @param {Array} dontcares - Array of don't care indices
 * @param {Array} varNames - Variable names
 * @param {string} mode - 'SOP' or 'POS'
 * @returns {Object} {implicants: [], result: string}
 */
function qmSimplify(minterms, dontcares, varNames, mode = 'SOP') {
  const allTerms = [...minterms, ...dontcares];
  if (!allTerms.length) {
    return { implicants: [], result: mode === 'SOP' ? '0' : '1' };
  }
  
  const W = varNames.length;
  const bins = allTerms.map(m => toBin(m, W));
  let groups = {};
  
  // Phase 1: Group by number of 1's
  for (const b of bins) {
    const k = countOnes(b);
    if (!groups[k]) groups[k] = [];
    groups[k].push({ bin: b, used: false, from: [b] });
  }

  let newGroups = {};
  let anyCombined = true;
  const allCombinedLevels = [];

  // Phase 2: Iterative combination
  while (anyCombined) {
    anyCombined = false;
    newGroups = {};
    const keys = Object.keys(groups).map(Number).sort((a, b) => a - b);
    
    // Combine adjacent groups
    for (let idx = 0; idx < keys.length - 1; idx++) {
      const k1 = keys[idx];
      const k2 = keys[idx + 1];
      const g1 = groups[k1] || [];
      const g2 = groups[k2] || [];
      
      for (const a of g1) {
        for (const b of g2) {
          if (canCombine(a.bin, b.bin)) {
            const c = combine(a.bin, b.bin);
            const ones = countOnes(c.replace(/-/g, ''));
            const item = {
              bin: c,
              used: false,
              from: [...new Set([...(a.from || []), ...(b.from || [])])]
            };
            
            if (!newGroups[ones]) newGroups[ones] = [];
            newGroups[ones].push(item);
            
            a.used = true;
            b.used = true;
            anyCombined = true;
          }
        }
      }
    }
    
    // Deduplicate new groups
    for (const k in newGroups) {
      const unique = [];
      const seen = new Set();
      for (const it of newGroups[k]) {
        const key = it.bin + '|' + (it.from || []).join(',');
        if (!seen.has(key)) {
          seen.add(key);
          unique.push(it);
        }
      }
      newGroups[k] = unique;
    }
    
    // Collect prime implicants (unused terms)
    const primes = [];
    for (const k in groups) {
      for (const it of groups[k]) {
        if (!it.used) primes.push(it.bin);
      }
    }
    allCombinedLevels.push(primes);
    groups = newGroups;
  }
  
  // Phase 3: Collect all prime implicants
  const finalPrimes = new Set();
  for (const arr of allCombinedLevels) {
    for (const p of arr) finalPrimes.add(p);
  }
  for (const k in groups) {
    for (const it of groups[k]) finalPrimes.add(it.bin);
  }
  const primeList = Array.from(finalPrimes);

  // Phase 4: Prime implicant chart (cover only actual minterms, not don't cares)
  const minBin = minterms.map(m => toBin(m, W));
  const cover = {};
  
  for (let i = 0; i < minBin.length; i++) {
    cover[i] = [];
    for (let j = 0; j < primeList.length; j++) {
      if (covers(primeList[j], minBin[i])) {
        cover[i].push(j);
      }
    }
  }
  
  // Phase 5: Find essential prime implicants
  const chosen = new Set();
  const coveredRows = new Set();
  
  for (let i = 0; i < minBin.length; i++) {
    if (cover[i].length === 1) {
      const j = cover[i][0];
      chosen.add(j);
    }
  }
  
  // Helper: Mark covered rows
  const markCovered = () => {
    let changed = false;
    for (let i = 0; i < minBin.length; i++) {
      if (coveredRows.has(i)) continue;
      for (const j of (cover[i] || [])) {
        if (chosen.has(j)) {
          coveredRows.add(i);
          changed = true;
          break;
        }
      }
    }
    return changed;
  };
  markCovered();

  // Phase 6: Greedy covering for remaining rows
  while (coveredRows.size < minBin.length) {
    let bestJ = -1;
    let bestCoverCount = -1;
    
    for (let j = 0; j < primeList.length; j++) {
      if (!chosen.has(j)) {
        let count = 0;
        for (let i = 0; i < minBin.length; i++) {
          if (coveredRows.has(i)) continue;
          if (cover[i].includes(j)) count++;
        }
        if (count > bestCoverCount) {
          bestCoverCount = count;
          bestJ = j;
        }
      }
    }
    
    if (bestJ === -1) break; // Should not happen if input is valid
    chosen.add(bestJ);
    markCovered();
  }

  // Phase 7: Convert to SOP or POS
  const implicants = Array.from(chosen).map(j => primeList[j]);
  
  if (mode === 'SOP') {
    const sop = implicantsToSOP(implicants, varNames);
    return { implicants, result: sop };
  } else {
    const pos = implicantsToPOS(implicants, varNames);
    return { implicants, result: pos };
  }
}

/**
 * Convert implicants to SOP (Sum of Products) form
 */
function implicantsToSOP(impls, vars) {
  if (!impls.length) return '0';
  
  const parts = impls.map(mask => {
    let s = '';
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === '-') continue;
      const v = vars[i];
      s += (mask[i] === '1') ? v : (v + "'");
    }
    return s || '1';
  });
  
  return parts.join(' + ');
}

/**
 * Convert implicants to POS (Product of Sums) form
 */
function implicantsToPOS(impls, vars) {
  if (!impls.length) return '1';
  
  const parts = impls.map(mask => {
    let s = '';
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === '-') continue;
      const v = vars[i];
      if (s) s += ' + ';
      s += (mask[i] === '0') ? v : (v + "'");
    }
    return s ? '(' + s + ')' : '1';
  });
  
  return parts.join('');
}

/* =============================================================================
   6. K-MAP LAYOUT GENERATION
   Generate K-Map structure based on number of variables
============================================================================= */
/**
 * Generate K-Map layout for given number of variables
 * @param {number} nVars - Number of variables (1-4)
 * @returns {Object} Layout configuration with Gray code ordering
 */
function kmapLayoutForVars(nVars) {
  if (nVars === 1) {
    return {
      rows: [0, 1],
      cols: [0],
      rowVars: ['A'],
      colVars: [],
      index({ r, c }) {
        return GRAY2[r];
      }
    };
  }
  
  if (nVars === 2) {
    return {
      rows: GRAY2,
      cols: GRAY2,
      rowVars: ['A'],
      colVars: ['B'],
      index({ r, c }) {
        const A = GRAY2[r];
        const B = GRAY2[c];
        return (A << 1) | B;
      }
    };
  }
  
  if (nVars === 3) {
    return {
      rows: GRAY2,
      cols: GRAY4,
      rowVars: ['A'],
      colVars: ['B', 'C'],
      index({ r, c }) {
        const A = GRAY2[r];
        const BC = GRAY4[c];
        const B = (BC >> 1) & 1;
        const C = BC & 1;
        return (A << 2) | (B << 1) | C;
      }
    };
  }
  
  if (nVars === 4) {
    return {
      rows: GRAY4,
      cols: GRAY4,
      rowVars: ['A', 'B'],
      colVars: ['C', 'D'],
      index({ r, c }) {
        const AB = GRAY4[r];
        const CD = GRAY4[c];
        const A = (AB >> 1) & 1;
        const B = AB & 1;
        const C = (CD >> 1) & 1;
        const D = CD & 1;
        return (A << 3) | (B << 2) | (C << 1) | D;
      }
    };
  }
  
  return null;
}

/**
 * Format axis label for K-Map
 */
function prettyAxisLabel(vars) {
  if (!vars.length) return '—';
  return vars.join('');
}

/* =============================================================================
   7. TRUTH TABLE GENERATION
============================================================================= */
/**
 * Build complete truth table for given variables and expression
 * @param {Array} vars - Variable names
 * @param {Array} rpn - RPN expression
 * @returns {Array} Array of {m: minterm_index, env: {A:0, B:1}, y: output}
 */
function buildTruthTable(vars, rpn) {
  const rows = [];
  const n = vars.length;
  const total = 1 << n; // 2^n combinations
  
  for (let m = 0; m < total; m++) {
    const env = {};
    // Convert minterm index to variable values
    for (let i = 0; i < n; i++) {
      env[vars[i]] = (m >> (n - 1 - i)) & 1;
    }
    const y = rpn ? evalRPN(rpn, env) : 0;
    rows.push({ m, env, y });
  }
  
  return rows;
}

/**
 * Update truth table display
 * @param {Array} vars - Variable names
 * @param {Array} results - Array of output results (0 or 1)
 */
function updateTruthTable(vars, results) {
    const thead = els.ttHead;
    const tbody = els.ttBody;
    
    // Clear existing content
    thead.innerHTML = '';
    tbody.innerHTML = '';
    
    // Create fixed header row
    const tr = document.createElement('tr');
    ['A', 'B', 'C', 'Y', 'm'].forEach(col => {
        const th = document.createElement('th');
        th.textContent = col;
        tr.appendChild(th);
    });
    thead.appendChild(tr);
    
    // Fill data rows with fixed column order
    results.forEach((result, idx) => {
        const tr = document.createElement('tr');
        
        // Input columns (A,B,C)
        for(let i = 0; i < 3; i++) {
            const td = document.createElement('td');
            td.textContent = i < vars.length ? ((idx >> (vars.length-1-i)) & 1) : '-';
            tr.appendChild(td);
        }
        
        // Output column (Y)
        const tdY = document.createElement('td');
        tdY.textContent = result;
        tr.appendChild(tdY);
        
        // Minterm number (m)
        const tdM = document.createElement('td');
        tdM.textContent = `m${idx}`; 
        tdM.classList.add('muted');
        tr.appendChild(tdM);
        
        tbody.appendChild(tr);
    });
}

/* =============================================================================
   8. APPLICATION STATE & DOM ELEMENTS
============================================================================= */
const els = {
  // Input
  expr: $('expr'),
  mintermIO: $('minterm-io'),
  
  // Buttons
  btnEval: $('btn-eval'),
  btnClear: $('btn-clear'),
  btnValidate: $('btn-validate'),
  btnSimplify: $('btn-simplify'),
  btnReset: $('btn-reset'),
  btnExportImg: $('btn-export-img'),
  btnImport: $('btn-import'),
  btnExport: $('btn-export'),
  modeSOP: $('mode-sop'),
  modePOS: $('mode-pos'),
  themeToggle: $('theme-toggle'),
  
  // Display
  errorMessage: $('error-message'),
  successMessage: $('success-message'),
  varsPill: $('vars-pill'),
  mintermsPill: $('minterms-pill'),
  benchmark: $('benchmark'),
  benchTime: $('bench-time'),
  benchCells: $('bench-cells'),
  benchComplexity: $('bench-complexity'),
  ttHead: document.querySelector('#ttbl thead'),
  ttBody: document.querySelector('#ttbl tbody'),
  kmap: $('kmap'),
  rowlabel: $('rowlabel'),
  collabel: $('collabel'),
  outSimplified: $('out-simplified'),
  resultLabel: $('result-label'),
  mintermLabel: $('minterm-label'),
  
  // Stats
  statEvaluations: $('stat-evaluations'),
  statVars: $('stat-vars'),
  statMinterms: $('stat-minterms'),
  statTime: $('stat-time')
};

// Application state
let currentVars = [];
let currentRPN = null;
let currentKMap = { vars: [], n: 0, layout: null, cells: [], total: 0 };
let currentMode = 'SOP';
let stats = {
  evaluations: 0,
  lastVars: 0,
  lastMinterms: 0,
  lastTime: 0
};

/* =============================================================================
   9. UI HELPER FUNCTIONS
============================================================================= */
function showError(message) {
  els.errorMessage.textContent = '❌ ' + message;
  els.errorMessage.classList.add('show');
  els.successMessage.classList.remove('show');
}

function showSuccess(message) {
  els.successMessage.textContent = '✅ ' + message;
  els.successMessage.classList.add('show');
  els.errorMessage.classList.remove('show');
}

function hideMessages() {
  els.errorMessage.classList.remove('show');
  els.successMessage.classList.remove('show');
}

function updateStats() {
  els.statEvaluations.textContent = stats.evaluations;
  els.statVars.textContent = stats.lastVars;
  els.statMinterms.textContent = stats.lastMinterms;
  els.statTime.textContent = stats.lastTime.toFixed(2) + 'ms';
}

function setPills(vars, minterms, dontcares) {
  els.varsPill.textContent = `Variabel: ${vars.length ? vars.join(', ') : '—'}`;
  const dcStr = dontcares.length ? ` +d(${dontcares.join(',')})` : '';
  els.mintermsPill.textContent = `Minterm: ${minterms.length ? minterms.join(',') + dcStr : '—'}`;
}

function renderTruthTable(vars, rows) {
  const thv = vars.map(v => `<th>${v}</th>`).join('');
  els.ttHead.innerHTML = `<tr>${thv}<th>Y</th><th class="muted">m</th></tr>`;
  
  els.ttBody.innerHTML = rows.map(r => {
    const vs = vars.map(v => `<td>${r.env[v]}</td>`).join('');
    return `<tr>${vs}<td><b>${r.y}</b></td><td class="muted">${r.m}</td></tr>`;
  }).join('');
}

function initKMap(vars) {
  const n = Math.min(vars.length, MAX_VARS);
  const layout = kmapLayoutForVars(n);
  currentKMap = { 
    vars: vars.slice(0, n), 
    n, 
    layout, 
    cells: [], 
    total: (1 << n) 
  };
  currentKMap.cells = new Array(currentKMap.total).fill(0);

  if (!layout) {
    els.kmap.innerHTML = `<div class="muted">⚠ K-Map tersedia hanya hingga 4 variabel. Variabel terdeteksi: ${vars.length}.</div>`;
    els.rowlabel.textContent = '—';
    els.collabel.textContent = '—';
    return;
  }

  els.rowlabel.textContent = prettyAxisLabel(layout.rowVars);
  els.collabel.textContent = prettyAxisLabel(layout.colVars);

  const rows = layout.rows.length || 1;
  const cols = layout.cols.length || 1;

  els.kmap.style.gridTemplateColumns = `repeat(${cols}, 58px)`;
  els.kmap.innerHTML = '';

  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const idx = layout.index({ r, c });
      const div = document.createElement('div');
      div.className = 'kcell';
      div.dataset.index = idx;
      div.textContent = '0';
      div.title = `m${idx} - Klik untuk toggle (0→1→d→0)`;
      
      div.addEventListener('click', () => {
        const val = currentKMap.cells[idx];
        currentKMap.cells[idx] = val === 0 ? 1 : (val === 1 ? 'd' : 0);
        updateKMapCell(div, idx);
      });
      
      els.kmap.appendChild(div);
    }
  }
}

function updateKMapCell(div, idx) {
  const val = currentKMap.cells[idx];
  div.classList.remove('on', 'dc');
  
  if (val === 1) {
    div.classList.add('on');
    div.textContent = '1';
  } else if (val === 'd') {
    div.classList.add('dc');
    div.textContent = 'd';
  } else {
    div.textContent = '0';
  }
}

function paintKMapFromData(minterms, dontcares) {
  if (!currentKMap.layout) return;
  
  for (let i = 0; i < currentKMap.total; i++) {
    currentKMap.cells[i] = 0;
  }
  
  for (const m of minterms) {
    if (m >= 0 && m < currentKMap.total) {
      currentKMap.cells[m] = 1;
    }
  }
  
  for (const d of dontcares) {
    if (d >= 0 && d < currentKMap.total) {
      currentKMap.cells[d] = 'd';
    }
  }
  
  const children = els.kmap.children;
  for (let k = 0; k < children.length; k++) {
    const idx = Number(children[k].dataset.index);
    updateKMapCell(children[k], idx);
  }
}

function collectDataFromKMap() {
  if (!currentKMap || !currentKMap.cells) {
    console.warn('K-Map not initialized');
    return { minterms: [], dontcares: [] };
  }
  
  const minterms = [];
  const dontcares = [];
  
  for (let i = 0; i < currentKMap.total; i++) {
    if (currentKMap.cells[i] === 1) minterms.push(i);
    else if (currentKMap.cells[i] === 'd') dontcares.push(i);
  }
  
  return { 
    minterms: minterms.sort((a, b) => a - b), 
    dontcares: dontcares.sort((a, b) => a - b) 
  };
}

function simplifyFromKMap() {
  const n = currentKMap.n;
  const vars = currentKMap.vars;
  
  if (n === 0) {
    const y = currentKMap.cells[0] === 1 ? '1' : '0';
    els.outSimplified.textContent = y;
    return;
  }
  
  const { minterms: minterms1, dontcares } = collectDataFromKMap();
  let effectiveMinterms = minterms1;
  
  if (currentMode === 'POS') {
    const allTerms = new Array(currentKMap.total).fill(0).map((_, i) => i);
    const onAndDC = new Set([...minterms1, ...dontcares]);
    effectiveMinterms = allTerms.filter(m => !onAndDC.has(m));
  }
  
  const startTime = performance.now();
  const { result } = qmSimplify(effectiveMinterms, dontcares, vars, currentMode);
  const endTime = performance.now();
  
  const timeTaken = endTime - startTime;
  els.outSimplified.textContent = result;
  els.benchTime.textContent = `${timeTaken.toFixed(3)}ms`;
  els.benchCells.textContent = `${effectiveMinterms.length} terms, ${dontcares.length} DC`;
  els.benchComplexity.textContent = `O(3^${vars.length} × ${vars.length}²)`;
  els.benchmark.style.display = 'flex';
  
  stats.lastTime = timeTaken;
  stats.lastMinterms = minterms1.length;
  updateStats();
}

function parseTermInput(input) {
  const minterms = [];
  const dontcares = [];
  
  const dcMatch = input.match(/\+\s*d\s*\(([^)]+)\)/i);
  let mainPart = input;
  
  if (dcMatch) {
    const dcPart = dcMatch[1];
    dontcares.push(...dcPart.split(/[,\s]+/)
      .map(s => s.trim())
      .filter(Boolean)
      .map(Number)
      .filter(n => Number.isInteger(n) && n >= 0));
    mainPart = input.substring(0, dcMatch.index);
  }
  
  minterms.push(...mainPart.split(/[,\s]+/)
    .map(s => s.trim())
    .filter(Boolean)
    .map(Number)
    .filter(n => Number.isInteger(n) && n >= 0));
  
  return { minterms, dontcares };
}

/* =============================================================================
   10. IMAGE EXPORT FUNCTIONALITY
============================================================================= */
function exportKMapAsImage() {
  const kmapEl = els.kmap;
  
  if (!currentKMap.layout) {
    showError('K-Map tidak tersedia untuk ekspor');
    return;
  }
  
  const canvas = document.createElement('canvas');
  const cellSize = 70;
  const padding = 100;
  const rows = currentKMap.layout.rows.length || 1;
  const cols = currentKMap.layout.cols.length || 1;
  
  canvas.width = cols * cellSize + padding * 2;
  canvas.height = rows * cellSize + padding * 2 + 40;
  const ctx = canvas.getContext('2d');
  
  const isDark = document.body.dataset.theme === 'dark';
  ctx.fillStyle = isDark ? '#0f1a35' : '#ffffff';
  ctx.fillRect(0, 0, canvas.width, canvas.height);
  
  // Title
  ctx.fillStyle = isDark ? '#e8eefc' : '#1a2332';
  ctx.font = 'bold 18px sans-serif';
  ctx.textAlign = 'left';
  ctx.fillText('Karnaugh Map', padding, 35);
  
  // Mode indicator
  ctx.font = '14px sans-serif';
  ctx.fillStyle = isDark ? '#5aa4ff' : '#3a7bc8';
  ctx.fillText(`Mode: ${currentMode}`, padding, 55);
  ctx.fillText(`Rows: ${prettyAxisLabel(currentKMap.layout.rowVars)}`, padding, 75);
  ctx.fillText(`Cols: ${prettyAxisLabel(currentKMap.layout.colVars)}`, padding + 120, 75);
  
  // Draw cells
  const children = kmapEl.children;
  const startY = 90;
  
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const x = padding + c * cellSize;
      const y = startY + r * cellSize;
      const cellIdx = r * cols + c;
      const dataIdx = Number(children[cellIdx].dataset.index);
      const val = currentKMap.cells[dataIdx];
      
      // Cell background
      if (val === 1) {
        ctx.fillStyle = isDark ? '#2b966a' : '#10b981';
      } else if (val === 'd') {
        ctx.fillStyle = isDark ? '#6b5a2a' : '#f59e0b';
      } else {
        ctx.fillStyle = isDark ? '#243255' : '#e5e7eb';
      }
      
      ctx.fillRect(x, y, cellSize - 4, cellSize - 4);
      
      // Cell border
      ctx.strokeStyle = isDark ? '#1c2849' : '#d1d5db';
      ctx.lineWidth = 2;
      ctx.strokeRect(x, y, cellSize - 4, cellSize - 4);
      
      // Cell value
      ctx.fillStyle = val ? '#ffffff' : (isDark ? '#e8eefc' : '#1a2332');
      ctx.font = 'bold 24px sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(
        val === 'd' ? 'd' : (val || '0'), 
        x + cellSize / 2 - 2, 
        y + cellSize / 2 - 2
      );
      
      // Minterm index (small)
      ctx.font = '10px sans-serif';
      ctx.fillStyle = isDark ? '#9fb2d7' : '#6b7280';
      ctx.fillText(`m${dataIdx}`, x + cellSize / 2 - 2, y + cellSize - 12);
    }
  }
  
  // Footer
  ctx.font = '11px sans-serif';
  ctx.fillStyle = isDark ? '#9fb2d7' : '#6b7280';
  ctx.textAlign = 'center';
  ctx.fillText(
    'Generated by Boolean Algebra & K-Map Simulator - Kelompok Pusay',
    canvas.width / 2,
    canvas.height - 15
  );
  
  // Download
  canvas.toBlob(blob => {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `kmap_${currentMode}_${Date.now()}.png`;
    a.click();
    URL.revokeObjectURL(url);
    showSuccess('K-Map berhasil diekspor sebagai PNG');
  });
}

/* =============================================================================
   11. EVENT HANDLERS
============================================================================= */

// Safe event binding
function bindEvent(el, event, handler) {
    if (!el) {
        console.warn(`Element not found for ${event} event`);
        return;
    }
    el.addEventListener(event, handler);
}

// Evaluate Expression
bindEvent(els.btnEval, 'click', () => {
  hideMessages();

  try {
    const expr = els.expr.value.trim();
    
    if (!expr) {
      showError('Harap masukkan ekspresi Boolean');
      return;
    }
    
    const vars0 = extractVars(expr);
    
    if (vars0.length === 0) {
      showError('Tidak ada variabel yang terdeteksi dalam ekspresi');
      return;
    }
    
    if (vars0.length > MAX_TRUTH_TABLE_VARS) {
      showError(`Maksimal ${MAX_TRUTH_TABLE_VARS} variabel untuk tabel kebenaran`);
      return;
    }
    
    currentVars = vars0.slice(0, MAX_TRUTH_TABLE_VARS);
    currentRPN = toRPN(tokenize(expr));

    const rows = buildTruthTable(currentVars, currentRPN);
    renderTruthTable(currentVars, rows);

    const minFull = rows.filter(r => r.y === 1).map(r => r.m);
    const kVars = currentVars.slice(0, MAX_VARS);
    initKMap(kVars);

    if (currentVars.length <= MAX_VARS) {
      paintKMapFromData(minFull, []);
      
      let effectiveMinterms = minFull;
      if (currentMode === 'POS') {
        const allTerms = new Array(currentKMap.total).fill(0).map((_, i) => i);
        const onAndDC = new Set(minFull);
        effectiveMinterms = allTerms.filter(m => !onAndDC.has(m));
      }

      const startTimeQM = performance.now();
      const { result } = qmSimplify(effectiveMinterms, [], kVars, currentMode);
      const endTimeQM = performance.now();
      
      const timeTaken = endTimeQM - startTimeQM;
      els.outSimplified.textContent = result;
      els.benchTime.textContent = `${timeTaken.toFixed(3)}ms`;
      els.benchCells.textContent = `${effectiveMinterms.length} terms`;
      els.benchComplexity.textContent = `O(3^${kVars.length} × ${kVars.length}²)`;
      els.benchmark.style.display = 'flex';
      
      stats.lastTime = timeTaken;
      stats.lastMinterms = minFull.length;
    } else {
      els.outSimplified.textContent = '— (K-Map hanya untuk ≤4 variabel)';
      els.benchmark.style.display = 'none';
    }

    setPills(currentVars, minFull, []);
    
    stats.evaluations++;
    stats.lastVars = currentVars.length;
    updateStats();
    
    showSuccess(`Evaluasi berhasil! ${minFull.length} minterm ditemukan.`);
    
  } catch (e) {
    console.error('Error:', e);
    showError(e.message);
    setPills([], [], []);
    els.outSimplified.textContent = '—';
    els.benchmark.style.display = 'none';
  }
});

// Validate Syntax
bindEvent(els.btnValidate, 'click', () => {
  hideMessages();
  
  try {
    const expr = els.expr.value.trim();
    
    if (!expr) {
      showError('Harap masukkan ekspresi untuk divalidasi');
      return;
    }
    
    const tokens = tokenize(expr);
    const rpn = toRPN(tokens);
    const vars = extractVars(expr);
    
    showSuccess(`Sintaks valid! ${tokens.length} token, ${vars.length} variabel: ${vars.join(', ')}`);
  } catch (e) {
    showError('Sintaks tidak valid: ' + e.message);
  }
});

// Clear All
bindEvent(els.btnClear, 'click', () => {
  els.expr.value = '';
  currentVars = [];
  currentRPN = null;
  els.ttHead.innerHTML = '';
  els.ttBody.innerHTML = '';
  initKMap([]);
  els.outSimplified.textContent = '—';
  setPills([], [], []);
  els.mintermIO.value = '';
  els.benchmark.style.display = 'none';
  hideMessages();
  showSuccess('Semua data berhasil dibersihkan');
});

// Reset K-Map
bindEvent(els.btnReset, 'click', () => {
  paintKMapFromData([], []);
  els.outSimplified.textContent = '—';
  els.benchmark.style.display = 'none';
  showSuccess('K-Map berhasil direset');
});

// Simplify K-Map
bindEvent(els.btnSimplify, 'click', () => {
  hideMessages();
  
  try {
    simplifyFromKMap();
    showSuccess('Penyederhanaan berhasil menggunakan algoritma Quine-McCluskey');
  } catch (e) {
    showError('Gagal menyederhanakan: ' + e.message);
  }
});

// Import Minterm
bindEvent(els.btnImport, 'click', () => {
  hideMessages();
  
  try {
    const txt = els.mintermIO.value.trim();
    
    if (!txt) {
      paintKMapFromData([], []);
      els.outSimplified.textContent = '—';
      showError('Input minterm kosong');
      return;
    }
    
    const { minterms, dontcares } = parseTermInput(txt);
    
    if (minterms.length === 0 && dontcares.length === 0) {
      showError('Tidak ada minterm valid yang ditemukan');
      return;
    }
    
    paintKMapFromData(minterms, dontcares);
    simplifyFromKMap();
    setPills(currentKMap.vars, minterms, dontcares);
    
    showSuccess(`Berhasil mengimpor ${minterms.length} minterm, ${dontcares.length} don't care`);
  } catch (e) {
    showError('Format minterm tidak valid: ' + e.message);
  }
});

// Export Minterm
bindEvent(els.btnExport, 'click', () => {
  const { minterms, dontcares } = collectDataFromKMap();
  let result = minterms.join(',');
  if (dontcares.length) result += ` +d(${dontcares.join(',')})`;
  
  els.mintermIO.value = result;
  
  if (minterms.length === 0 && dontcares.length === 0) {
    showError('K-Map kosong, tidak ada yang diekspor');
  } else {
    showSuccess(`Berhasil mengekspor ${minterms.length} minterm, ${dontcares.length} don't care`);
  }
});

// Export Image
bindEvent(els.btnExportImg, 'click', () => {
  hideMessages();
  exportKMapAsImage();
});

// Mode Toggle: SOP
bindEvent(els.modeSOP, 'click', () => {
  currentMode = 'SOP';
  els.modeSOP.classList.add('active');
  els.modePOS.classList.remove('active');
  els.resultLabel.innerHTML = '🎯 Hasil Penyederhanaan (SOP) <span class="tooltip-icon" data-tip="Sum of Products - bentuk penjumlahan dari product terms">?</span>';
  els.mintermLabel.innerHTML = '📥 Import/Export Minterm <span class="tooltip-icon" data-tip="Format: 0,1,5,7 atau 0,1,5,7+d(2,3)">?</span>';
  
  if (currentKMap.layout) {
    simplifyFromKMap();
  }
});

// Mode Toggle: POS
bindEvent(els.modePOS, 'click', () => {
  currentMode = 'POS';
  els.modePOS.classList.add('active');
  els.modeSOP.classList.remove('active');
  els.resultLabel.innerHTML = '🎯 Hasil Penyederhanaan (POS) <span class="tooltip-icon" data-tip="Product of Sums - bentuk perkalian dari sum terms">?</span>';
  els.mintermLabel.innerHTML = '📥 Import/Export Maxterm <span class="tooltip-icon" data-tip="Format: 0,1,5,7 atau 0,1,5,7+d(2,3)">?</span>';
  
  if (currentKMap.layout) {
    simplifyFromKMap();
  }
});

// Theme Toggle
bindEvent(els.themeToggle, 'click', () => {
  const current = document.body.dataset.theme;
  const newTheme = current === 'dark' ? 'light' : 'dark';
  document.body.dataset.theme = newTheme;
  localStorage.setItem('theme', newTheme);
  
  showSuccess(`Tema berhasil diubah ke ${newTheme === 'dark' ? 'Dark' : 'Light'} mode`);
  setTimeout(hideMessages, 2000);
});

// Example Buttons
document.querySelectorAll('.example-btn').forEach(btn => {
  btn.addEventListener('click', () => {
    els.expr.value = btn.dataset.expr;
    els.btnEval.click();
  });
});

// Keyboard Shortcuts
document.addEventListener('keydown', (e) => {
  if (e.ctrlKey || e.metaKey) {
    if (e.key === 'Enter') {
      e.preventDefault();
      els.btnEval.click();
    } else if (e.key === 'k') {
      e.preventDefault();
      els.expr.focus();
    }
  }
});

/* =============================================================================
   12. INITIALIZATION
============================================================================= */
function init() {
  // Load saved theme
  const savedTheme = localStorage.getItem('theme') || 'dark';
  document.body.dataset.theme = savedTheme;
  
  // Initialize K-Map
  initKMap([]);
  setPills([], [], []);
  updateStats();
  
  // Auto-focus input
  els.expr.focus();
  
  console.log('%c🎓 Boolean Algebra & K-Map Simulator', 'font-size: 16px; font-weight: bold; color: #46b07b;');
  console.log('%cKelompok Pusay - Sistem Digital', 'font-size: 12px; color: #5aa4ff;');
  console.log('%cKeyboard Shortcuts:', 'font-size: 12px; font-weight: bold; margin-top: 8px;');
  console.log('  Ctrl+Enter: Evaluate expression');
  console.log('  Ctrl+K: Focus input field');
}

// Run initialization
init();

// Sakura Animation
function createSakura() {
  const sakura = document.createElement('div');
  sakura.className = 'sakura';
  
  // Random properties
  const left = Math.random() * 100;
  const animationDuration = Math.random() * 3 + 2;
  const size = Math.random() * 5 + 10;
  
  sakura.style.left = `${left}vw`;
  sakura.style.animationDuration = `${animationDuration}s`;
  sakura.style.width = `${size}px`;
  sakura.style.height = `${size}px`;
  
  document.querySelector('.sakura-container').appendChild(sakura);
  
  // Remove after animation
  setTimeout(() => {
    sakura.remove();
  }, animationDuration * 1000);
}

// Create sakura periodically
setInterval(createSakura, 300);

/* =============================================================================
   AVATAR ANIMATION INIT
============================================================================= */
(function avatarInit(){
  const avatar = document.getElementById('anime-avatar');
  if (!avatar) { console.warn('anime-avatar not found'); return; }

  // hide/show on click
  avatar.addEventListener('click', () => {
    avatar.style.opacity = avatar.style.opacity === '0' ? '1' : '0';
    avatar.style.transition = 'opacity .3s ease, transform .18s ease';
  });

  // fallback if file missing
  avatar.addEventListener('error', () => {
    avatar.style.display = 'none';
    console.warn('Failed to load character.png — check path: web/assets/character.png');
  });

  // small entrance animation
  avatar.style.transform = 'translateY(0)';
  avatar.animate([
    { transform: 'translateY(-8px)', opacity: 0 },
    { transform: 'translateY(0)', opacity: 1 }
  ], { duration: 450, easing: 'cubic-bezier(.2,.8,.2,1)' });
})();

// Anime Character Greeting System
const greetings = [
  "Selamat datang! 💫",
  "Hai~ senang kamu datang ke sini! 💖",
  "Halo! Siap bantu logika boolean-mu hari ini?",
  "Yoroshiku~ semangat belajar ya! 🌸",
  "Selamat datang kembali, pahlawan data! ⚡",
  "Boolean itu mudah kalau kita pahami! 💡",
  "Mari belajar K-Map bersama! 📚",
  "Jangan lupa istirahat ya! 🍵"
];

function showGreeting() {
    const bubble = document.querySelector('.speech-bubble');
    const greetingText = document.querySelector('.greeting-text');
    
    if (!bubble || !greetingText) return;
    
    // Random greeting
    const randomGreeting = greetings[Math.floor(Math.random() * greetings.length)];
    greetingText.textContent = randomGreeting;
    
    // Show bubble
    bubble.style.opacity = '1';
    bubble.style.transform = 'translateY(0)';
    
    // Hide bubble after 7 seconds
    setTimeout(() => {
        bubble.style.opacity = '0';
        bubble.style.transform = 'translateY(20px)';
    }, 7000);
}

// Initialize greeting system
function initCharacterGreeting() {
    showGreeting(); // Show initial greeting
    
    // Set interval for 50 seconds
    setInterval(() => {
        showGreeting();
    }, 50000); // 50 seconds in milliseconds
}

// Start when DOM is loaded
document.addEventListener('DOMContentLoaded', initCharacterGreeting);
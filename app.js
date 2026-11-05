(() => {
  'use strict';

  const GLYPHS = {
    w: { K: '♔', Q: '♕', R: '♖', B: '♗', N: '♘', P: '♙' },
    b: { K: '♚', Q: '♛', R: '♜', B: '♝', N: '♞', P: '♟' }
  };
  const NAMES = { K: 'King', Q: 'Queen', R: 'Rook', B: 'Bishop', N: 'Knight', P: 'Pawn' };
  const ABBR = { K: 'K', Q: 'Q', R: 'R', B: 'B', N: 'N', P: 'P' };
  const FILES = 'abcdefgh';
  const boardEl = document.getElementById('board');
  const $ = id => document.getElementById(id);
  let state, selected = null, legalForSelection = [], legalMoves = [], undoStack = [], log = [], flipped = false, pendingPromotion = null, toastTimer;

  function createInitialState() {
    let nextId = 0;
    const board = Array.from({ length: 8 }, () => Array(8).fill(null));
    const back = ['R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R'];
    for (let c = 0; c < 8; c++) {
      for (const [r, color, type] of [[0, 'b', back[c]], [1, 'b', 'P'], [6, 'w', 'P'], [7, 'w', back[c]]]) {
        const piece = { id: `${color}${++nextId}`, color, type, original: type, moved: false };
        board[r][c] = piece;
        if (type === 'K') stateKings[color] = piece.id;
        if (type === 'R') {
          if (c === 0) stateRooks[color].q = piece.id;
          if (c === 7) stateRooks[color].k = piece.id;
        }
      }
    }
    return { board, turn: 'w', ep: null, kings: { ...stateKings }, rooks: { w: { ...stateRooks.w }, b: { ...stateRooks.b } }, captured: { w: [], b: [] }, lastMove: null, over: false, outcome: null };
  }
  let stateKings = {}, stateRooks = { w: {}, b: {} };

  function cloneState(source) {
    return {
      ...source,
      board: source.board.map(row => row.map(p => p ? { ...p } : null)),
      kings: { ...source.kings },
      rooks: { w: { ...source.rooks.w }, b: { ...source.rooks.b } },
      captured: { w: source.captured.w.map(p => ({ ...p })), b: source.captured.b.map(p => ({ ...p })) },
      ep: source.ep ? { ...source.ep } : null,
      lastMove: source.lastMove ? { ...source.lastMove } : null,
      outcome: source.outcome ? { ...source.outcome } : null
    };
  }
  const inside = (r, c) => r >= 0 && r < 8 && c >= 0 && c < 8;
  const opponent = color => color === 'w' ? 'b' : 'w';
  const squareName = (r, c) => `${FILES[c]}${8 - r}`;
  const findKing = (s, color) => {
    const id = s.kings[color];
    for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) if (s.board[r][c]?.id === id) return { r, c };
    return null;
  };

  function attacked(s, r, c, byColor) {
    const pawnSourceRow = r + (byColor === 'w' ? 1 : -1);
    for (const dc of [-1, 1]) if (inside(pawnSourceRow, c + dc)) {
      const p = s.board[pawnSourceRow][c + dc];
      if (p?.color === byColor && p.type === 'P') return true;
    }
    for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) {
      const rr = r + dr, cc = c + dc;
      if (inside(rr, cc) && s.board[rr][cc]?.color === byColor && s.board[rr][cc].type === 'N') return true;
    }
    for (const [dr, dc] of [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]]) {
      let rr = r + dr, cc = c + dc, distance = 1;
      while (inside(rr, cc)) {
        const p = s.board[rr][cc];
        if (p) {
          if (p.color === byColor) {
            if (p.type === 'Q' || (distance === 1 && p.type === 'K') || (dr === 0 || dc === 0 ? p.type === 'R' : p.type === 'B')) return true;
          }
          break;
        }
        rr += dr; cc += dc; distance++;
      }
    }
    return false;
  }
  function inCheck(s, color) {
    const king = findKing(s, color);
    return !!king && attacked(s, king.r, king.c, opponent(color));
  }

  function pseudoMoves(s, r, c) {
    const p = s.board[r][c];
    if (!p) return [];
    const moves = [], add = (rr, cc, extra = {}) => {
      if (!inside(rr, cc)) return false;
      const target = s.board[rr][cc];
      if (target?.color === p.color || target?.type === 'K') return false;
      moves.push({ from: { r, c }, to: { r: rr, c: cc }, ...extra });
      return !target;
    };
    if (p.type === 'P') {
      const dir = p.color === 'w' ? -1 : 1, start = p.color === 'w' ? 6 : 1;
      const one = r + dir;
      if (inside(one, c) && !s.board[one][c]) {
        add(one, c);
        if (r === start && !p.moved && !s.board[r + 2 * dir][c]) add(r + 2 * dir, c, { double: true });
      }
      for (const dc of [-1, 1]) {
        const rr = r + dir, cc = c + dc;
        if (!inside(rr, cc)) continue;
        if (s.board[rr][cc] && s.board[rr][cc].color !== p.color && s.board[rr][cc].type !== 'K') add(rr, cc);
        else if (s.ep && s.ep.r === rr && s.ep.c === cc) moves.push({ from: { r, c }, to: { r: rr, c: cc }, ep: true });
      }
      return moves;
    }
    if (p.type === 'N') {
      for (const [dr, dc] of [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]]) add(r + dr, c + dc);
      return moves;
    }
    if (p.type === 'K') {
      for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) if (dr || dc) add(r + dr, c + dc);
      if (!p.moved && p.id === s.kings[p.color] && !inCheck(s, p.color)) {
        const home = p.color === 'w' ? 7 : 0;
        for (const side of ['k', 'q']) {
          const rookId = s.rooks[p.color][side], rookCol = side === 'k' ? 7 : 0;
          const rook = s.board[home][rookCol];
          const emptyCols = side === 'k' ? [5, 6] : [1, 2, 3];
          const transitCols = side === 'k' ? [5, 6] : [3, 2];
          if (r !== home || c !== 4 || !rook || rook.id !== rookId || rook.type !== 'R' || rook.moved) continue;
          if (emptyCols.some(col => s.board[home][col])) continue;
          if (transitCols.some(col => attacked(s, home, col, opponent(p.color)))) continue;
          moves.push({ from: { r, c }, to: { r: home, c: side === 'k' ? 6 : 2 }, castle: side });
        }
      }
      return moves;
    }
    const dirs = [];
    if (p.type === 'R' || p.type === 'Q') dirs.push([-1,0], [1,0], [0,-1], [0,1]);
    if (p.type === 'B' || p.type === 'Q') dirs.push([-1,-1], [-1,1], [1,-1], [1,1]);
    for (const [dr, dc] of dirs) {
      let rr = r + dr, cc = c + dc;
      while (add(rr, cc)) { rr += dr; cc += dc; }
    }
    return moves;
  }

  function applyMove(s, move, promotion = null) {
    const { r: fr, c: fc } = move.from, { r: tr, c: tc } = move.to;
    const piece = s.board[fr][fc];
    let captured = move.ep ? s.board[fr][tc] : s.board[tr][tc];
    if (move.ep) s.board[fr][tc] = null;
    s.board[fr][fc] = null;
    if (captured) {
      captured = { ...captured };
      s.captured[piece.color].push(captured);
      if (piece.type !== 'K') piece.type = captured.type;
    }
    piece.moved = true;
    s.board[tr][tc] = piece;
    if (move.castle) {
      const rookFrom = move.castle === 'k' ? 7 : 0, rookTo = move.castle === 'k' ? 5 : 3;
      const rook = s.board[tr][rookFrom];
      s.board[tr][rookFrom] = null;
      s.board[tr][rookTo] = rook;
      rook.moved = true;
    }
    if (promotion && piece.type === 'P' && (tr === 0 || tr === 7)) piece.type = promotion;
    s.ep = move.double ? { r: (fr + tr) / 2, c: fc, pawn: piece.id } : null;
    s.lastMove = { from: { ...move.from }, to: { ...move.to } };
    return { piece, captured };
  }

  function legalFor(s, r, c) {
    const piece = s.board[r][c];
    if (!piece) return [];
    return pseudoMoves(s, r, c).filter(move => {
      const test = cloneState(s);
      applyMove(test, move, 'Q');
      return !inCheck(test, piece.color);
    });
  }
  function allLegal(s, color) {
    const moves = [];
    for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) {
      if (s.board[r][c]?.color === color) moves.push(...legalFor(s, r, c));
    }
    return moves;
  }

  function updateGameStatus() {
    legalMoves = allLegal(state, state.turn);
    const check = inCheck(state, state.turn);
    if (!legalMoves.length) {
      state.over = true;
      state.outcome = check ? { type: 'mate', winner: opponent(state.turn) } : { type: 'draw' };
      if (log.length) log[log.length - 1].suffix = check ? '#' : '½';
    } else if (log.length) {
      log[log.length - 1].suffix = check ? '+' : '';
    }
    render();
  }

  function render() {
    renderBoard(); renderSidePanel(); renderStatus();
  }
  function renderBoard() {
    boardEl.innerHTML = '';
    const rowOrder = flipped ? [0,1,2,3,4,5,6,7] : [7,6,5,4,3,2,1,0];
    const colOrder = flipped ? [7,6,5,4,3,2,1,0] : [0,1,2,3,4,5,6,7];
    const checkedKing = inCheck(state, state.turn) ? findKing(state, state.turn) : null;
    for (const r of rowOrder) for (const c of colOrder) {
      const square = document.createElement('button');
      square.type = 'button'; square.className = `square ${(r + c) % 2 ? 'dark' : 'light'}`;
      square.dataset.r = r; square.dataset.c = c; square.setAttribute('role', 'gridcell');
      const piece = state.board[r][c], name = squareName(r, c);
      square.setAttribute('aria-label', `${name}${piece ? ` ${piece.color === 'w' ? 'white' : 'black'} ${NAMES[piece.type]}` : ''}`);
      if (state.lastMove && ((state.lastMove.from.r === r && state.lastMove.from.c === c) || (state.lastMove.to.r === r && state.lastMove.to.c === c))) square.classList.add('last-move');
      if (selected && selected.r === r && selected.c === c) square.classList.add('selected');
      if (checkedKing && checkedKing.r === r && checkedKing.c === c) square.classList.add('in-check');
      if (piece) {
        const glyph = document.createElement('span'); glyph.className = `piece ${piece.color === 'w' ? 'white' : 'black'}`; glyph.textContent = GLYPHS[piece.color][piece.type];
        square.appendChild(glyph);
        if (piece.type !== piece.original) { const badge = document.createElement('span'); badge.className = 'power-badge'; badge.textContent = ABBR[piece.type]; badge.title = `Power changed from ${NAMES[piece.original]} to ${NAMES[piece.type]}`; square.appendChild(badge); }
      }
      if (selected && legalForSelection.some(m => m.to.r === r && m.to.c === c)) {
        const capture = state.board[r][c] || legalForSelection.find(m => m.to.r === r && m.to.c === c)?.ep;
        const mark = document.createElement('span'); mark.className = capture ? 'legal-capture' : 'legal-dot'; square.appendChild(mark);
      }
      square.addEventListener('click', onSquareClick);
      boardEl.appendChild(square);
    }
    const files = flipped ? [...FILES].reverse() : [...FILES];
    const ranks = flipped ? ['1','2','3','4','5','6','7','8'] : ['8','7','6','5','4','3','2','1'];
    for (const id of ['filesTop','filesBottom']) $(id).innerHTML = files.map((f,i)=>`<span class="coordinate ${i%2===0?'dark-coordinate':''}">${f}</span>`).join('');
    for (const id of ['ranksLeft','ranksRight']) $(id).innerHTML = ranks.map((n,i)=>`<span class="coordinate ${i%2===0?'dark-coordinate':''}">${n}</span>`).join('');
  }
  function renderSidePanel() {
    for (const color of ['w', 'b']) {
      let count = 0;
      for (const row of state.board) for (const p of row) if (p?.color === color) count++;
      $(`${color === 'w' ? 'white' : 'black'}Summary`).textContent = `${count} ${count === 1 ? 'piece' : 'pieces'} · ${color === state.turn && !state.over ? 'to play' : 'on board'}`;
      $(`${color === 'w' ? 'white' : 'black'}Check`).classList.toggle('hidden', !(color === state.turn && inCheck(state, color) && !state.over));
      const tray = $(`${color === 'w' ? 'white' : 'black'}Captured`);
      tray.innerHTML = state.captured[color].map(p => `<span class="captured-piece ${p.color === 'w' ? 'light-piece' : 'dark-piece'}" title="${p.color === 'w' ? 'White' : 'Black'} ${NAMES[p.type]}">${GLYPHS[p.color][p.type]}</span>`).join('');
    }
    const counts = { K: 0, Q: 0, R: 0, B: 0, N: 0, P: 0 };
    for (const row of state.board) for (const p of row) if (p) counts[p.type]++;
    $('powerList').innerHTML = ['Q','R','B','N','P','K'].map(type => `<div class="power-item ${counts[type] ? '' : 'is-zero'}"><span class="power-glyph">${GLYPHS.w[type]}</span><span class="power-name"><strong>${NAMES[type]}</strong><small>${String(counts[type]).padStart(2,'0')} ACTIVE</small></span></div>`).join('');
    $('historyCount').textContent = `${log.length} ${log.length === 1 ? 'PLY' : 'PLIES'}`;
    if (!log.length) $('historyList').innerHTML = '<div class="empty-history"><span>↗</span><p>Your first move<br>starts the story.</p></div>';
    else {
      const rows = [];
      for (let i = 0; i < log.length; i += 2) rows.push(`<div class="history-row"><span class="history-index">${String(i / 2 + 1).padStart(2,'0')}</span><span class="history-move">${log[i].text}${log[i].suffix || ''}</span><span class="history-move">${log[i + 1] ? `${log[i + 1].text}${log[i + 1].suffix || ''}` : ''}</span></div>`);
      $('historyList').innerHTML = rows.join(''); $('historyList').scrollTop = $('historyList').scrollHeight;
    }
    $('undoButton').disabled = undoStack.length === 0 || !!pendingPromotion;
    $('moveCount').textContent = `MOVE ${String(Math.floor(log.length / 2) + 1).padStart(2, '0')}`;
  }
  function renderStatus() {
    const turn = state.turn, check = inCheck(state, turn);
    const king = $('turnKing'); king.textContent = GLYPHS[turn].K; king.classList.toggle('black-turn', turn === 'b');
    $('turnCard').classList.toggle('game-over', state.over);
    $('turnIndicator').style.color = turn === 'w' ? 'var(--lime)' : '#d4ddd4';
    $('turnEyebrow').textContent = state.over ? 'GAME COMPLETE' : `${turn === 'w' ? 'WHITE' : 'BLACK'} TO MOVE`;
    if (state.outcome?.type === 'mate') {
      $('turnTitle').textContent = `${state.outcome.winner === 'w' ? 'White' : 'Black'} wins`;
      $('turnMessage').textContent = 'Checkmate. What a finish.';
      $('footerState').textContent = 'CHECKMATE';
    } else if (state.outcome?.type === 'draw') {
      $('turnTitle').textContent = 'It’s a draw'; $('turnMessage').textContent = 'No legal moves — stalemate.'; $('footerState').textContent = 'STALEMATE';
    } else if (check) {
      $('turnTitle').textContent = turn === 'w' ? 'You’re in check' : 'Black is in check';
      $('turnMessage').textContent = 'Find a way out of danger.'; $('footerState').textContent = 'CHECK';
    } else {
      $('turnTitle').textContent = turn === 'w' ? 'Your move' : 'Black to move';
      $('turnMessage').textContent = selected ? 'Choose a highlighted square.' : (log.length ? 'The board is yours.' : 'Choose a piece to begin.');
      $('footerState').textContent = 'LOCAL GAME';
    }
  }

  function onSquareClick(event) {
    if (state.over || pendingPromotion) return;
    const r = Number(event.currentTarget.dataset.r), c = Number(event.currentTarget.dataset.c), piece = state.board[r][c];
    if (selected) {
      const match = legalForSelection.find(m => m.to.r === r && m.to.c === c);
      if (match) { beginMove(match); return; }
      if (piece?.color === state.turn) { selectSquare(r, c); return; }
      clearSelection(); return;
    }
    if (piece?.color === state.turn) selectSquare(r, c);
  }
  function selectSquare(r, c) {
    selected = { r, c }; legalForSelection = legalFor(state, r, c); render();
  }
  function clearSelection() { selected = null; legalForSelection = []; render(); }
  function beginMove(move) {
    const before = cloneState(state), mover = state.board[move.from.r][move.from.c], target = move.ep ? state.board[move.from.r][move.to.c] : state.board[move.to.r][move.to.c];
    const from = squareName(move.from.r, move.from.c), to = squareName(move.to.r, move.to.c);
    const movingType = mover.type;
    const notation = movingType === 'P' ? (target || move.ep ? from[0] + 'x' + to : to) : `${ABBR[movingType]}${target || move.ep ? 'x' : ''}${to}`;
    applyMove(state, move);
    const piece = state.board[move.to.r][move.to.c];
    selected = null; legalForSelection = [];
    if (piece.type === 'P' && (move.to.r === 0 || move.to.r === 7)) {
      pendingPromotion = { before, move, notation, pieceId: piece.id };
      render(); showPromotion(piece.color); return;
    }
    completeMove(before, notation);
  }
  function completeMove(before, notation) {
    undoStack.push(before);
    log.push({ text: notation, suffix: '' });
    state.turn = opponent(state.turn);
    pendingPromotion = null;
    updateGameStatus();
  }
  function showPromotion(color) {
    const options = ['Q','R','B','N'];
    $('promotionOptions').innerHTML = options.map(type => `<button class="promotion-choice" data-type="${type}"><span class="piece ${color === 'w' ? 'white' : 'black'}">${GLYPHS[color][type]}</span><small>${NAMES[type].toUpperCase()}</small></button>`).join('');
    $('promotionBackdrop').classList.remove('hidden');
    $('promotionOptions').querySelectorAll('button').forEach(button => button.addEventListener('click', () => {
      const type = button.dataset.type;
      for (const row of state.board) for (const piece of row) if (piece?.id === pendingPromotion.pieceId) piece.type = type;
      $('promotionBackdrop').classList.add('hidden');
      completeMove(pendingPromotion.before, `${pendingPromotion.notation}=${ABBR[type]}`);
    }));
  }

  function resetGame() {
    stateKings = {}; stateRooks = { w: {}, b: {} }; state = createInitialState();
    selected = null; legalForSelection = []; legalMoves = []; undoStack = []; log = []; pendingPromotion = null;
    $('promotionBackdrop').classList.add('hidden'); updateGameStatus();
  }
  function undoMove() {
    if (!undoStack.length || pendingPromotion) return;
    state = undoStack.pop(); log.pop(); selected = null; legalForSelection = []; updateGameStatus();
  }
  function showToast(message) {
    const el = $('toast'); el.textContent = message; el.classList.add('show'); clearTimeout(toastTimer); toastTimer = setTimeout(() => el.classList.remove('show'), 1800);
  }
  function showRules() { $('modalBackdrop').classList.remove('hidden'); }
  $('newGameButton').addEventListener('click', () => {
    if (log.length && !state.over && !confirm('Start a new game? Your current game will be lost.')) return;
    flipped = false; resetGame(); showToast('Fresh board. New possibilities.');
  });
  $('undoButton').addEventListener('click', undoMove);
  $('flipButton').addEventListener('click', () => { flipped = !flipped; renderBoard(); });
  $('rulesButton').addEventListener('click', showRules);
  $('modalClose').addEventListener('click', () => $('modalBackdrop').classList.add('hidden'));
  $('modalAction').addEventListener('click', () => $('modalBackdrop').classList.add('hidden'));
  $('modalBackdrop').addEventListener('click', e => { if (e.target === $('modalBackdrop')) $('modalBackdrop').classList.add('hidden'); });
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape') {
      if (!$('modalBackdrop').classList.contains('hidden')) $('modalBackdrop').classList.add('hidden');
      else if (selected) clearSelection();
    }
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); undoMove(); }
  });

  resetGame();
})();

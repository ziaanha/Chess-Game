
"use strict";

/* =========================================================
   ZÉA CHESS
   Vanilla JavaScript chess game and computer opponent
   ========================================================= */

const $ = (selector) => document.querySelector(selector);

const boardElement = $("#chessboard");
const messageElement = $("#game-message");
const moveListElement = $("#move-list");
const moveCountElement = $("#move-count");

const gameModeSelect = $("#game-mode");
const playerColorSelect = $("#player-color");
const difficultySelect = $("#difficulty");
const timeControlSelect = $("#time-control");

const whiteClockElement = $("#white-clock");
const blackClockElement = $("#black-clock");

const promotionDialog = $("#promotion-dialog");
const resultDialog = $("#result-dialog");

const PIECES = {
  w: { k: "♔", q: "♕", r: "♖", b: "♗", n: "♘", p: "♙" },
  b: { k: "♚", q: "♛", r: "♜", b: "♝", n: "♞", p: "♟" }
};

const PIECE_NAMES = {
  k: "king",
  q: "queen",
  r: "rook",
  b: "bishop",
  n: "knight",
  p: "pawn"
};

const PIECE_VALUES = {
  k: 20000,
  q: 900,
  r: 500,
  b: 330,
  n: 320,
  p: 100
};

const FILES = "abcdefgh";

let state;
let selectedSquare = null;
let selectedMoves = [];
let flipped = false;
let lastMove = null;
let pendingPromotion = null;
let computerThinking = false;
let gameToken = 0;
let clockInterval = null;
let lastClockTick = Date.now();
let clockSeconds = { w: 600, b: 600 };
let gameStarted = false;
let gameOver = false;

/* -------------------------
   Board and game setup
   ------------------------- */

function makeInitialBoard() {
  const board = Array.from({ length: 8 }, () => Array(8).fill(null));
  const backRank = ["r", "n", "b", "q", "k", "b", "n", "r"];

  for (let col = 0; col < 8; col++) {
    board[0][col] = { type: backRank[col], color: "b" };
    board[1][col] = { type: "p", color: "b" };
    board[6][col] = { type: "p", color: "w" };
    board[7][col] = { type: backRank[col], color: "w" };
  }

  return board;
}

function initialState() {
  return {
    board: makeInitialBoard(),
    turn: "w",
    castling: {
      wK: true,
      wQ: true,
      bK: true,
      bQ: true
    },
    enPassant: null,
    halfmove: 0,
    fullmove: 1,
    history: [],
    moves: [],
    captured: { w: [], b: [] },
    lastMove: null
  };
}

function cloneState(source) {
  return {
    board: source.board.map(row =>
      row.map(piece => piece ? { ...piece } : null)
    ),
    turn: source.turn,
    castling: { ...source.castling },
    enPassant: source.enPassant ? { ...source.enPassant } : null,
    halfmove: source.halfmove,
    fullmove: source.fullmove,
    history: [],
    moves: [],
    captured: {
      w: [...source.captured.w],
      b: [...source.captured.b]
    },
    lastMove: source.lastMove
      ? {
          from: { ...source.lastMove.from },
          to: { ...source.lastMove.to }
        }
      : null
  };
}

function snapshotState(source) {
  return {
    board: source.board.map(row =>
      row.map(piece => piece ? { ...piece } : null)
    ),
    turn: source.turn,
    castling: { ...source.castling },
    enPassant: source.enPassant ? { ...source.enPassant } : null,
    halfmove: source.halfmove,
    fullmove: source.fullmove,
    moves: [...source.moves],
    captured: {
      w: [...source.captured.w],
      b: [...source.captured.b]
    },
    lastMove: source.lastMove
      ? {
          from: { ...source.lastMove.from },
          to: { ...source.lastMove.to }
        }
      : null
  };
}

function restoreSnapshot(snapshot) {
  state.board = snapshot.board.map(row =>
    row.map(piece => piece ? { ...piece } : null)
  );
  state.turn = snapshot.turn;
  state.castling = { ...snapshot.castling };
  state.enPassant = snapshot.enPassant
    ? { ...snapshot.enPassant }
    : null;
  state.halfmove = snapshot.halfmove;
  state.fullmove = snapshot.fullmove;
  state.moves = [...snapshot.moves];
  state.captured = {
    w: [...snapshot.captured.w],
    b: [...snapshot.captured.b]
  };
  state.lastMove = snapshot.lastMove
    ? {
        from: { ...snapshot.lastMove.from },
        to: { ...snapshot.lastMove.to }
      }
    : null;
}

/* -------------------------
   Coordinates and attacks
   ------------------------- */

function insideBoard(row, col) {
  return row >= 0 && row < 8 && col >= 0 && col < 8;
}

function squareName(square) {
  return FILES[square.col] + (8 - square.row);
}

function findKing(position, color) {
  for (let row = 0; row < 8; row++) {
    for (let col = 0; col < 8; col++) {
      const piece = position.board[row][col];
      if (piece && piece.color === color && piece.type === "k") {
        return { row, col };
      }
    }
  }
  return null;
}

function isSquareAttacked(position, row, col, byColor) {
  const board = position.board;

  // Pawn attacks
  const pawnRow = row + (byColor === "w" ? 1 : -1);

  for (const dc of [-1, 1]) {
    const pc = col + dc;

    if (insideBoard(pawnRow, pc)) {
      const piece = board[pawnRow][pc];
      if (piece && piece.color === byColor && piece.type === "p") {
        return true;
      }
    }
  }

  // Knight attacks
  const knightOffsets = [
    [-2, -1], [-2, 1], [-1, -2], [-1, 2],
    [1, -2], [1, 2], [2, -1], [2, 1]
  ];

  for (const [dr, dc] of knightOffsets) {
    const r = row + dr;
    const c = col + dc;

    if (!insideBoard(r, c)) continue;

    const piece = board[r][c];
    if (piece && piece.color === byColor && piece.type === "n") {
      return true;
    }
  }

  // King attacks
  for (let dr = -1; dr <= 1; dr++) {
    for (let dc = -1; dc <= 1; dc++) {
      if (dr === 0 && dc === 0) continue;

      const r = row + dr;
      const c = col + dc;

      if (!insideBoard(r, c)) continue;

      const piece = board[r][c];
      if (piece && piece.color === byColor && piece.type === "k") {
        return true;
      }
    }
  }

  // Sliding piece attacks
  const directions = [
    [-1, 0], [1, 0], [0, -1], [0, 1],
    [-1, -1], [-1, 1], [1, -1], [1, 1]
  ];

  for (const [dr, dc] of directions) {
    let r = row + dr;
    let c = col + dc;
    let distance = 1;

    while (insideBoard(r, c)) {
      const piece = board[r][c];

      if (piece) {
        if (piece.color === byColor) {
          const diagonal = dr !== 0 && dc !== 0;
          const straight = dr === 0 || dc === 0;

          if (
            piece.type === "q" ||
            (diagonal && piece.type === "b") ||
            (straight && piece.type === "r") ||
            (distance === 1 && piece.type === "k")
          ) {
            return true;
          }
        }

        break;
      }

      r += dr;
      c += dc;
      distance++;
    }
  }

  return false;
}

function isInCheck(position, color) {
  const king = findKing(position, color);

  if (!king) return true;

  return isSquareAttacked(
    position,
    king.row,
    king.col,
    color === "w" ? "b" : "w"
  );
}

/* -------------------------
   Pseudo-legal moves
   ------------------------- */

function addMove(moves, fromRow, fromCol, row, col, extras = {}) {
  if (!insideBoard(row, col)) return;

  const target = state.board[row][col];

  // This helper is only used with state temporarily switched below.
  // Move generation itself uses the explicit position in each function.
  moves.push({
    from: { row: fromRow, col: fromCol },
    to: { row, col },
    ...extras
  });
}

function pseudoMoves(position, row, col) {
  const board = position.board;
  const piece = board[row][col];
  const moves = [];

  if (!piece) return moves;

  const { type, color } = piece;
  const direction = color === "w" ? -1 : 1;

  function push(r, c, extras = {}) {
    if (!insideBoard(r, c)) return;

    const target = board[r][c];

    if (target && target.color === color) return;
    if (target && target.type === "k") return;

    moves.push({
      from: { row, col },
      to: { row: r, col: c },
      ...extras
    });
  }

  if (type === "p") {
    const nextRow = row + direction;
    const promotionRow = color === "w" ? 0 : 7;
    const startRow = color === "w" ? 6 : 1;

    if (
      insideBoard(nextRow, col) &&
      !board[nextRow][col]
    ) {
      push(nextRow, col);

      if (
        nextRow !== promotionRow &&
        row === startRow &&
        !board[row + 2 * direction][col]
      ) {
        push(row + 2 * direction, col, { doublePawn: true });
      }
    }

    for (const dc of [-1, 1]) {
      const targetRow = row + direction;
      const targetCol = col + dc;

      if (!insideBoard(targetRow, targetCol)) continue;

      const target = board[targetRow][targetCol];

      if (target && target.color !== color && target.type !== "k") {
        push(targetRow, targetCol);
      } else if (
        position.enPassant &&
        position.enPassant.row === targetRow &&
        position.enPassant.col === targetCol
      ) {
        push(targetRow, targetCol, { enPassant: true });
      }
    }

    return moves.map(move =>
      move.to.row === promotionRow
        ? { ...move, promotion: "q" }
        : move
    );
  }

  if (type === "n") {
    const offsets = [
      [-2, -1], [-2, 1], [-1, -2], [-1, 2],
      [1, -2], [1, 2], [2, -1], [2, 1]
    ];

    for (const [dr, dc] of offsets) {
      push(row + dr, col + dc);
    }

    return moves;
  }

  if (type === "k") {
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (dr === 0 && dc === 0) continue;
        push(row + dr, col + dc);
      }
    }

    // Castling
    const homeRow = color === "w" ? 7 : 0;
    const enemy = color === "w" ? "b" : "w";
    const canCastleKingSide = position.castling[color + "K"];
    const canCastleQueenSide = position.castling[color + "Q"];

    if (
      row === homeRow &&
      col === 4 &&
      !isSquareAttacked(position, homeRow, 4, enemy)
    ) {
      // King-side: e1/e8 to g1/g8
      if (
        canCastleKingSide &&
        board[homeRow][5] === null &&
        board[homeRow][6] === null &&
        board[homeRow][7] &&
        board[homeRow][7].type === "r" &&
        board[homeRow][7].color === color &&
        !isSquareAttacked(position, homeRow, 5, enemy) &&
        !isSquareAttacked(position, homeRow, 6, enemy)
      ) {
        push(homeRow, 6, { castle: "king" });
      }

      // Queen-side: e1/e8 to c1/c8
      if (
        canCastleQueenSide &&
        board[homeRow][1] === null &&
        board[homeRow][2] === null &&
        board[homeRow][3] === null &&
        board[homeRow][0] &&
        board[homeRow][0].type === "r" &&
        board[homeRow][0].color === color &&
        !isSquareAttacked(position, homeRow, 3, enemy) &&
        !isSquareAttacked(position, homeRow, 2, enemy)
      ) {
        push(homeRow, 2, { castle: "queen" });
      }
    }

    return moves;
  }

  const directions = [];

  if (type === "b" || type === "q") {
    directions.push(
      [-1, -1], [-1, 1], [1, -1], [1, 1]
    );
  }

  if (type === "r" || type === "q") {
    directions.push(
      [-1, 0], [1, 0], [0, -1], [0, 1]
    );
  }

  for (const [dr, dc] of directions) {
    let r = row + dr;
    let c = col + dc;

    while (insideBoard(r, c)) {
      const target = board[r][c];

      if (!target) {
        push(r, c);
      } else {
        if (target.color !== color && target.type !== "k") {
          push(r, c);
        }
        break;
      }

      r += dr;
      c += dc;
    }
  }

  return moves;
}

/* -------------------------
   Applying and validating moves
   ------------------------- */

function applyMove(position, move) {
  const board = position.board;
  const from = move.from;
  const to = move.to;
  const piece = board[from.row][from.col];

  if (!piece) return null;

  const movingPiece = { ...piece };
  let captured = board[to.row][to.col]
    ? { ...board[to.row][to.col] }
    : null;

  if (move.enPassant) {
    const capturedRow = to.row + (piece.color === "w" ? 1 : -1);
    captured = board[capturedRow][to.col]
      ? { ...board[capturedRow][to.col] }
      : null;
    board[capturedRow][to.col] = null;
  }

  board[from.row][from.col] = null;

  if (move.promotion) {
    movingPiece.type = move.promotion;
  }

  board[to.row][to.col] = movingPiece;

  if (move.castle) {
    const homeRow = piece.color === "w" ? 7 : 0;

    if (move.castle === "king") {
      board[homeRow][5] = board[homeRow][7];
      board[homeRow][7] = null;
    } else {
      board[homeRow][3] = board[homeRow][0];
      board[homeRow][0] = null;
    }
  }

  // Moving a king removes both castling rights.
  if (piece.type === "k") {
    position.castling[piece.color + "K"] = false;
    position.castling[piece.color + "Q"] = false;
  }

  // Moving a rook from its original square removes that side's right.
  if (piece.type === "r") {
    if (from.row === 7 && from.col === 0) position.castling.wQ = false;
    if (from.row === 7 && from.col === 7) position.castling.wK = false;
    if (from.row === 0 && from.col === 0) position.castling.bQ = false;
    if (from.row === 0 && from.col === 7) position.castling.bK = false;
  }

  // Capturing a rook on its original square removes that side's right.
  if (captured && captured.type === "r") {
    if (to.row === 7 && to.col === 0) position.castling.wQ = false;
    if (to.row === 7 && to.col === 7) position.castling.wK = false;
    if (to.row === 0 && to.col === 0) position.castling.bQ = false;
    if (to.row === 0 && to.col === 7) position.castling.bK = false;
  }

  position.enPassant = null;

  if (piece.type === "p" && Math.abs(to.row - from.row) === 2) {
    position.enPassant = {
      row: (to.row + from.row) / 2,
      col: from.col
    };
  }

  position.halfmove =
    piece.type === "p" || captured
      ? 0
      : position.halfmove + 1;

  if (position.turn === "b") {
    position.fullmove++;
  }

  position.turn = position.turn === "w" ? "b" : "w";

  position.lastMove = {
    from: { ...from },
    to: { ...to }
  };

  return { piece, captured };
}

function legalMoves(position, row, col) {
  const piece = position.board[row][col];

  if (!piece) return [];

  const moves = pseudoMoves(position, row, col);

  return moves.filter(move => {
    const copy = cloneState(position);
    applyMove(copy, move);
    return !isInCheck(copy, piece.color);
  });
}

function allLegalMoves(position, color = position.turn) {
  const moves = [];

  for (let row = 0; row < 8; row++) {
    for (let col = 0; col < 8; col++) {
      const piece = position.board[row][col];

      if (piece && piece.color === color) {
        moves.push(...legalMoves(position, row, col));
      }
    }
  }

  return moves;
}

function sameSquare(a, b) {
  return a && b && a.row === b.row && a.col === b.col;
}

function findMove(moves, destination) {
  return moves.find(move => sameSquare(move.to, destination));
}

/* -------------------------
   Rendering the board
   ------------------------- */

function renderBoard() {
  boardElement.innerHTML = "";

  const checkKing = findKing(state, state.turn);
  const kingInCheck = checkKing && isInCheck(state, state.turn);

  for (let displayRow = 0; displayRow < 8; displayRow++) {
    for (let displayCol = 0; displayCol < 8; displayCol++) {
      const row = flipped ? 7 - displayRow : displayRow;
      const col = flipped ? 7 - displayCol : displayCol;

      const piece = state.board[row][col];
      const square = document.createElement("button");

      square.type = "button";
      square.className =
        "square " + ((row + col) % 2 === 0 ? "light" : "dark");

      square.dataset.row = row;
      square.dataset.col = col;
      square.setAttribute("role", "gridcell");

      const coordinate = squareName({ row, col });
      square.setAttribute(
        "aria-label",
        coordinate + (piece
          ? ", " + piece.color + " " + PIECE_NAMES[piece.type]
          : ", empty")
      );

      if (selectedSquare && sameSquare(selectedSquare, { row, col })) {
        square.classList.add("selected");
      }

      if (
        state.lastMove &&
        (sameSquare(state.lastMove.from, { row, col }) ||
          sameSquare(state.lastMove.to, { row, col }))
      ) {
        square.classList.add("last-move");
      }

      const availableMove = selectedMoves.find(move =>
        sameSquare(move.to, { row, col })
      );

      if (availableMove) {
        square.classList.add(
          piece || availableMove.enPassant
            ? "legal-capture"
            : "legal-move"
        );
      }

      if (
        kingInCheck &&
        piece &&
        piece.type === "k" &&
        piece.color === state.turn
      ) {
        square.classList.add("in-check");
      }

      if (piece) {
        const pieceElement = document.createElement("span");
        pieceElement.className =
          "chess-piece " +
          (piece.color === "w" ? "piece-white" : "piece-black");
        pieceElement.textContent = PIECES[piece.color][piece.type];
        pieceElement.setAttribute("aria-hidden", "true");
        square.appendChild(pieceElement);
      }

      boardElement.appendChild(square);
    }
  }

  renderCoordinates();
}

function renderCoordinates() {
  const files = $(".board-files");
  const ranks = $(".board-ranks");

  const fileOrder = flipped
    ? [...FILES].reverse()
    : [...FILES];

  const rankOrder = flipped
    ? ["1", "2", "3", "4", "5", "6", "7", "8"]
    : ["8", "7", "6", "5", "4", "3", "2", "1"];

  files.innerHTML = fileOrder.map(file => `<span>${file}</span>`).join("");
  ranks.innerHTML = rankOrder.map(rank => `<span>${rank}</span>`).join("");
}

function renderMoveHistory() {
  moveListElement.innerHTML = "";

  if (state.moves.length === 0) {
    const empty = document.createElement("div");
    empty.className = "empty-state";
    empty.innerHTML = `
      <span class="empty-icon">♙</span>
      <p>Your moves will appear here.</p>
      <small>Make the first move to begin.</small>
    `;
    moveListElement.appendChild(empty);
  } else {
    for (let i = 0; i < state.moves.length; i += 2) {
      const row = document.createElement("div");
      row.className = "move-row";

      const number = document.createElement("span");
      number.className = "move-number";
      number.textContent = `${Math.floor(i / 2) + 1}.`;

      const whiteMove = document.createElement("span");
      whiteMove.className = "move-san";
      whiteMove.textContent = state.moves[i];

      const blackMove = document.createElement("span");
      blackMove.className = "move-san";
      blackMove.textContent = state.moves[i + 1] || "…";

      row.append(number, whiteMove, blackMove);
      moveListElement.appendChild(row);
    }

    moveListElement.scrollTop = moveListElement.scrollHeight;
  }

  const fullMoves = Math.ceil(state.moves.length / 2);
  moveCountElement.textContent =
    `${fullMoves} ${fullMoves === 1 ? "move" : "moves"}`;
}

function renderCapturedPieces() {
  for (const color of ["w", "b"]) {
    const target = color === "w"
      ? $("#white-captured")
      : $("#black-captured");

    target.textContent = "";

    if (state.captured[color].length === 0) {
      target.textContent = "—";
      continue;
    }

    for (const piece of state.captured[color]) {
      const span = document.createElement("span");
      span.textContent = PIECES[piece.color][piece.type];
      span.title = PIECE_NAMES[piece.type];
      target.appendChild(span);
    }
  }
}

function renderPlayers() {
  const mode = gameModeSelect.value;
  const playerColor = playerColorSelect.value;

  if (mode === "local") {
    $("#opponent-name").textContent = "Black";
    $("#opponent-description").textContent = "Local player";
    $("#current-name").textContent = "White";
    $("#current-description").textContent = "Local player";
    $("#opponent-avatar").textContent = "♚";
    $("#current-avatar").textContent = "♔";
  } else {
    $("#opponent-name").textContent =
      playerColor === "w" ? "ZÉA Computer" : "You";
    $("#opponent-description").textContent =
      playerColor === "w" ? "Black · Computer opponent" : "White · You";

    $("#current-name").textContent =
      playerColor === "w" ? "You" : "ZÉA Computer";
    $("#current-description").textContent =
      playerColor === "w" ? "White · You" : "Black · Computer opponent";

    $("#opponent-avatar").textContent =
      playerColor === "w" ? "♚" : "♔";
    $("#current-avatar").textContent =
      playerColor === "w" ? "♔" : "♚";
  }
}

function renderAll() {
  renderBoard();
  renderMoveHistory();
  renderCapturedPieces();
  renderPlayers();
  updateClockDisplay();
}

/* -------------------------
   Turn and result handling
   ------------------------- */

function isComputerTurn() {
  return (
    gameModeSelect.value === "computer" &&
    state.turn !== playerColorSelect.value
  );
}

function setMessage(message) {
  messageElement.textContent = message;
}

function getGameResult(position) {
  const moves = allLegalMoves(position);
  const checked = isInCheck(position, position.turn);

  if (moves.length === 0) {
    if (checked) {
      return {
        title: "Checkmate!",
        description: `${position.turn === "w" ? "Black" : "White"} wins.`,
        icon: "♛",
        winner: position.turn === "w" ? "b" : "w"
      };
    }

    return {
      title: "Draw by stalemate",
      description: "The player to move has no legal moves, but is not in check.",
      icon: "½",
      winner: null
    };
  }

  if (position.halfmove >= 100) {
    return {
      title: "Draw by 50-move rule",
      description: "No pawn move or capture occurred in the last 50 moves by each player.",
      icon: "½",
      winner: null
    };
  }

  if (isInsufficientMaterial(position)) {
    return {
      title: "Draw",
      description: "Neither side has enough material to force checkmate.",
      icon: "½",
      winner: null
    };
  }

  return null;
}

function isInsufficientMaterial(position) {
  const pieces = [];

  for (let row = 0; row < 8; row++) {
    for (let col = 0; col < 8; col++) {
      const piece = position.board[row][col];
      if (piece && piece.type !== "k") {
        pieces.push({ ...piece, row, col });
      }
    }
  }

  if (pieces.length === 0) return true;

  if (
    pieces.length === 1 &&
    ["b", "n"].includes(pieces[0].type)
  ) {
    return true;
  }

  if (pieces.every(piece => piece.type === "b")) {
    const squareColors = pieces.map(piece =>
      (piece.row + piece.col) % 2
    );
    return squareColors.every(color => color === squareColors[0]);
  }

  return false;
}

function checkGameEnd() {
  const result = getGameResult(state);

  if (result) {
    finishGame(result.title, result.description, result.icon);
    return true;
  }

  if (isInCheck(state, state.turn)) {
    setMessage(
      `${state.turn === "w" ? "White" : "Black"} is in check!`
    );
  } else if (isComputerTurn()) {
    setMessage("ZÉA Computer is thinking…");
  } else {
    setMessage(`${state.turn === "w" ? "White" : "Black"} to move`);
  }

  return false;
}

function finishGame(title, description, icon = "♔") {
  gameOver = true;
  computerThinking = false;
  gameToken++;
  stopClock();

  $("#result-title").textContent = title;
  $("#result-description").textContent = description;
  $("#result-icon").textContent = icon;

  if (!resultDialog.open) resultDialog.showModal();
}

function closeResult() {
  if (resultDialog.open) resultDialog.close();
}

/* -------------------------
   Move notation
   ------------------------- */

function moveNotation(position, move, piece, captured) {
  if (move.castle === "king") return "O-O";
  if (move.castle === "queen") return "O-O-O";

  const from = squareName(move.from);
  const to = squareName(move.to);
  const capture = captured || move.enPassant ? "x" : "-";
  let notation = "";

  if (piece.type === "p") {
    if (capture === "x") notation += from[0];
  } else {
    notation += piece.type.toUpperCase();
  }

  notation += capture + to;

  if (move.promotion) {
    notation += "=" + move.promotion.toUpperCase();
  }

  return notation;
}

/* -------------------------
   Human move input
   ------------------------- */

function onBoardClick(event) {
  if (gameOver || computerThinking || pendingPromotion) return;
  if (isComputerTurn()) return;

  const square = event.target.closest(".square");
  if (!square) return;

  const row = Number(square.dataset.row);
  const col = Number(square.dataset.col);
  const clicked = { row, col };
  const piece = state.board[row][col];

  if (selectedSquare) {
    const move = findMove(selectedMoves, clicked);

    if (move) {
      if (move.promotion) {
        openPromotion(move);
      } else {
        commitMove(move);
      }
      return;
    }

    if (piece && piece.color === state.turn) {
      selectSquare(clicked);
      return;
    }

    clearSelection();
    renderBoard();
    return;
  }

  if (piece && piece.color === state.turn) {
    selectSquare(clicked);
  }
}

function selectSquare(square) {
  const piece = state.board[square.row][square.col];

  if (!piece || piece.color !== state.turn) return;

  selectedSquare = square;
  selectedMoves = legalMoves(state, square.row, square.col);
  renderBoard();
}

function clearSelection() {
  selectedSquare = null;
  selectedMoves = [];
}

function openPromotion(move) {
  pendingPromotion = move;

  const color = state.turn;

  promotionDialog.querySelectorAll("[data-piece]").forEach(button => {
    const type = button.dataset.piece;
    button.textContent = PIECES[color][type];
  });

  promotionDialog.showModal();
}

function closePromotion() {
  pendingPromotion = null;
  if (promotionDialog.open) promotionDialog.close();
}

/* -------------------------
   Commit a real move
   ------------------------- */

function commitMove(move) {
  if (gameOver) return;

  const before = snapshotState(state);
  const piece = state.board[move.from.row][move.from.col];

  if (!piece) return;

  const previousTurn = state.turn;
  const result = applyMove(state, move);

  if (!result) return;

  const { captured } = result;

  state.history.push(before);

  if (captured) {
    state.captured[previousTurn].push(captured);
  }

  let notation = moveNotation(before, move, piece, captured);
  state.moves.push(notation);

  clearSelection();
  closePromotion();

  // A clock starts when the first move is made.
  if (!gameStarted) {
    gameStarted = true;
    lastClockTick = Date.now();
    startClock();
  }

  renderAll();

  if (checkGameEnd()) return;

  if (isComputerTurn()) {
    computerThinking = true;
    renderPlayers();
    setMessage("ZÉA Computer is thinking…");
    scheduleComputerMove();
  }
}

/* -------------------------
   Computer opponent
   ------------------------- */

function evaluatePosition(position, aiColor) {
  let score = 0;

  for (let row = 0; row < 8; row++) {
    for (let col = 0; col < 8; col++) {
      const piece = position.board[row][col];
      if (!piece) continue;

      const sign = piece.color === aiColor ? 1 : -1;
      let value = PIECE_VALUES[piece.type];

      // Encourage minor pieces and pawns to develop toward the center.
      const centerDistance =
        Math.abs(3.5 - row) + Math.abs(3.5 - col);
      const centrality = 7 - centerDistance;

      if (piece.type === "p") {
        value += (piece.color === "w" ? 6 - row : row - 1) * 7;
        value += centrality * 3;
      } else if (["n", "b"].includes(piece.type)) {
        value += centrality * 7;
      } else if (piece.type === "q") {
        value += centrality * 2;
      }

      score += sign * value;
    }
  }

  return score;
}

function orderMoves(position, moves) {
  return moves.slice().sort((a, b) => {
    function score(move) {
      const moving = position.board[move.from.row][move.from.col];
      const target = position.board[move.to.row][move.to.col];
      let value = 0;

      if (target) {
        value += 10 * PIECE_VALUES[target.type] -
          PIECE_VALUES[moving.type];
      }

      if (move.enPassant) value += 900;
      if (move.promotion) value += PIECE_VALUES[move.promotion];
      if (move.castle) value += 30;

      return value;
    }

    return score(b) - score(a);
  });
}

function search(position, depth, alpha, beta, aiColor, ply = 0) {
  const moves = allLegalMoves(position);

  if (moves.length === 0) {
    if (isInCheck(position, position.turn)) {
      return position.turn === aiColor
        ? -100000 + ply
        : 100000 - ply;
    }
    return 0;
  }

  if (position.halfmove >= 100 || isInsufficientMaterial(position)) {
    return 0;
  }

  if (depth === 0) {
    return evaluatePosition(position, aiColor);
  }

  const maximizing = position.turn === aiColor;
  const ordered = orderMoves(position, moves);

  if (maximizing) {
    let best = -Infinity;

    for (const move of ordered) {
      const next = cloneState(position);
      applyMove(next, move);

      const score = search(
        next, depth - 1, alpha, beta, aiColor, ply + 1
      );

      best = Math.max(best, score);
      alpha = Math.max(alpha, best);

      if (beta <= alpha) break;
    }

    return best;
  }

  let best = Infinity;

  for (const move of ordered) {
    const next = cloneState(position);
    applyMove(next, move);

    const score = search(
      next, depth - 1, alpha, beta, aiColor, ply + 1
    );

    best = Math.min(best, score);
    beta = Math.min(beta, best);

    if (beta <= alpha) break;
  }

  return best;
}

function chooseComputerMove() {
  const moves = allLegalMoves(state);

  if (moves.length === 0) return null;

  const difficulty = difficultySelect.value;
  const depth = difficulty === "easy" ? 1 :
    difficulty === "medium" ? 2 : 3;

  // Easy mode sometimes chooses a random legal move.
  if (difficulty === "easy" && Math.random() < 0.35) {
    return moves[Math.floor(Math.random() * moves.length)];
  }

  const aiColor = state.turn;
  const ordered = orderMoves(state, moves);

  let bestMove = null;
  let bestScore = -Infinity;
  let alpha = -Infinity;
  const beta = Infinity;

  for (const move of ordered) {
    const next = cloneState(state);
    applyMove(next, move);

    const score = search(
      next, depth - 1, alpha, beta, aiColor, 1
    );

    if (score > bestScore) {
      bestScore = score;
      bestMove = move;
    }

    alpha = Math.max(alpha, bestScore);
  }

  return bestMove || moves[0];
}

function scheduleComputerMove() {
  const token = gameToken;

  // Allow the browser to display the thinking message first.
  window.setTimeout(() => {
    if (token !== gameToken || gameOver || !isComputerTurn()) {
      computerThinking = false;
      return;
    }

    const move = chooseComputerMove();

    if (token !== gameToken || gameOver) return;

    computerThinking = false;

    if (move) {
      commitMove(move);
    } else {
      checkGameEnd();
    }
  }, 250);
}

/* -------------------------
   Undo, restart, resign
   ------------------------- */

function undoMove() {
  if (state.history.length === 0) return;

  closeResult();
  closePromotion();

  // In computer mode, undo the computer's move and your previous move
  // together, when both are available.
  let count = 1;

  if (
    gameModeSelect.value === "computer" &&
    state.history.length >= 2
  ) {
    count = 2;
  }

  for (let i = 0; i < count; i++) {
    const snapshot = state.history.pop();
    if (snapshot) restoreSnapshot(snapshot);
  }

  gameOver = false;
  computerThinking = false;
  gameToken++;
  clearSelection();

  renderAll();
  checkGameEnd();
}

function startNewGame() {
  gameToken++;
  stopClock();
  closeResult();
  closePromotion();

  state = initialState();
  selectedSquare = null;
  selectedMoves = [];
  pendingPromotion = null;
  computerThinking = false;
  gameStarted = false;
  gameOver = false;
  lastMove = null;
  flipped = false;

  const time = Number(timeControlSelect.value);
  clockSeconds = { w: time, b: time };

  renderAll();
  setMessage("White to move");

  if (gameModeSelect.value === "computer") {
    if (playerColorSelect.value === "b") {
      computerThinking = true;
      setMessage("ZÉA Computer is thinking…");
      scheduleComputerMove();
    }
  }
}

function resignGame() {
  if (gameOver) return;

  const winner = state.turn === "w" ? "Black" : "White";
  finishGame("Game resigned", `${winner} wins by resignation.`, "♟");
}

/* -------------------------
   Chess clocks
   ------------------------- */

function formatTime(seconds) {
  if (seconds <= 0) return "0:00";

  const minutes = Math.floor(seconds / 60);
  const remaining = seconds % 60;

  return `${minutes}:${String(remaining).padStart(2, "0")}`;
}

function updateClockDisplay() {
  whiteClockElement.textContent = formatTime(clockSeconds.w);
  blackClockElement.textContent = formatTime(clockSeconds.b);

  whiteClockElement.classList.toggle(
    "clock-active",
    gameStarted && !gameOver && state.turn === "w"
  );

  blackClockElement.classList.toggle(
    "clock-active",
    gameStarted && !gameOver && state.turn === "b"
  );
}

function startClock() {
  if (clockInterval || Number(timeControlSelect.value) === 0) return;

  lastClockTick = Date.now();

  clockInterval = window.setInterval(() => {
    if (gameOver || !gameStarted) return;

    const now = Date.now();
    const elapsed = Math.floor((now - lastClockTick) / 1000);

    if (elapsed < 1) return;

    lastClockTick += elapsed * 1000;
    clockSeconds[state.turn] -= elapsed;

    if (clockSeconds[state.turn] <= 0) {
      clockSeconds[state.turn] = 0;
      updateClockDisplay();

      const loser = state.turn === "w" ? "White" : "Black";
      const winner = state.turn === "w" ? "Black" : "White";

      finishGame(
        "Time's up!",
        `${loser} ran out of time. ${winner} wins on time.`,
        "⏱"
      );

      return;
    }

    updateClockDisplay();
  }, 250);
}

function stopClock() {
  if (clockInterval) {
    clearInterval(clockInterval);
    clockInterval = null;
  }
}

/* -------------------------
   Theme and event listeners
   ------------------------- */

boardElement.addEventListener("click", onBoardClick);

$("#new-game-button").addEventListener("click", startNewGame);
$("#undo-button").addEventListener("click", undoMove);
$("#resign-button").addEventListener("click", resignGame);

$("#flip-button").addEventListener("click", () => {
  flipped = !flipped;
  renderBoard();
});

$("#theme-toggle").addEventListener("click", () => {
  document.body.classList.toggle("dark-theme");
});

gameModeSelect.addEventListener("change", () => {
  $("#computer-settings").hidden = gameModeSelect.value !== "computer";
  startNewGame();
});

playerColorSelect.addEventListener("change", startNewGame);
difficultySelect.addEventListener("change", () => {
  // The new difficulty applies to the next computer move.
});
timeControlSelect.addEventListener("change", startNewGame);

$("#play-again-button").addEventListener("click", startNewGame);

$("#close-result-button").addEventListener("click", closeResult);

promotionDialog.querySelectorAll("[data-piece]").forEach(button => {
  button.addEventListener("click", () => {
    if (!pendingPromotion) return;

    const move = {
      ...pendingPromotion,
      promotion: button.dataset.piece
    };

    closePromotion();
    commitMove(move);
  });
});

promotionDialog.addEventListener("cancel", () => {
  pendingPromotion = null;
  clearSelection();
  renderBoard();
});

resultDialog.addEventListener("cancel", () => {
  // Allow the player to close the result and inspect the final board.
});

$("#computer-settings").hidden = gameModeSelect.value !== "computer";

/* -------------------------
   Start the game
   ------------------------- */

startNewGame();

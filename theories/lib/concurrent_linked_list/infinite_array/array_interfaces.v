From iris.heap_lang Require Export notation.

Record infiniteArrayInterface :=
  InfiniteArrayInterface {
      newInfiniteArray: val;
      onCancelledCell: val;
      findCell: val;
      derefCellPointer: val;
      cutoffMoveForward: val;
      cutoffGetPointer: val;
      cellPointerId: val;
      cellPointerCleanPrev: val;
    }.

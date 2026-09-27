# nonogram

`nonogram_helper.lua` is a Matcha overlay for the walk-to-fill nonogram game (place 96277935599613). It reads the board, solves it, paints the answer, and can walk the answer in for you (auto fill).

- **F8**: show or hide the overlay
- **F7**: arm or disarm auto fill
- **F6**: replay how the board was solved

Auto fill is persistent. Once it's armed, only F7 (or `_G.nonogram.autofill(false)` / `.stop()`) disarms it. When something goes wrong (mistakes, getting stuck, fill mode that won't switch, errors), it backs off or sits out the current board, then resumes on the next one. Re-running the script keeps it armed. Set `CFG.autoArm = true` to arm it on start. `_G.nonogram.autoinfo()` shows what it's doing.

The header of the script lists the full console API.

## Tests

```
lua5.1 tests/run.lua
```

The tests mock the Roblox and Matcha APIs, so they run offline. They check the solver and that auto fill stays armed through trouble.

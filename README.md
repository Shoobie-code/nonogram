# nonogram

`nonogram_helper.lua` is a Matcha overlay for the walk-to-fill nonogram game (place 96277935599613). It reads the board, solves it, paints the answer, and can walk the answer in for you (auto fill).

- **F8**: show or hide the overlay
- **F7**: arm or disarm auto fill
- **F6**: turn the live solving view on or off

Auto fill is persistent. Once it's armed, only F7 (or `_G.nonogram.autofill(false)` / `.stop()`) disarms it. When something goes wrong (mistakes, getting stuck, fill mode that won't switch, errors), it backs off or sits out the current board, then resumes on the next one. Re-running the script keeps it armed. Set `CFG.autoArm = true` to arm it on start. `_G.nonogram.autoinfo()` shows what it's doing.

The live solving view is on by default. The solver records every step while it solves a board, and the view plays those steps back on the overlay as soon as the solve finishes (a moment after the board spawns):
- a blue outline marks the row or column being read
- white flashes mark the tiles that step proves
- purple outlines mark what a tile would imply when the solver tries it both ways
- orange outlines mark guesses and dead ends once logic runs out

Only solid tiles are the answer; outlines never are.

Turning the view on with F6 solves the current board again and plays that. It stays on for every board, and across re-runs, until you press F6 again. The answer overlay and auto fill never wait for the playback.

The header of the script lists the full console API.

## Tests

```
lua5.1 tests/run.lua
```

The tests mock the Roblox and Matcha APIs, so they run offline. They check the solver, the live view, and that auto fill stays armed through trouble.

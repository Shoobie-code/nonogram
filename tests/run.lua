-- Offline tests: lua5.1 tests/run.lua (from the repo root)
-- Mocks just enough of Roblox + Matcha to load nonogram_helper.lua, then
-- checks the solver core and that auto fill stays armed through trouble.

local SCRIPT = "nonogram_helper.lua"
local fails, passes = 0, 0
local function check(cond, what)
	if cond then passes = passes + 1 else fails = fails + 1; io.write("FAIL: ", what, "\n") end
end

------------------------------------------------------------------------------
-- mock world
------------------------------------------------------------------------------
local T = 0
os.clock = function() return T end

local function V3(x, y, z) return { X = x, Y = y, Z = z } end
Vector3 = { new = V3 }
Vector2 = { new = function(x, y) return { X = x, Y = y } end }
Color3 = { fromRGB = function(r, g, b) return { r, g, b } end }

local function inst(name, props)
	local o = props or {}
	o.Name, o._kids, o._attr = name, {}, o._attr or {}
	function o:GetChildren() local t = {} for i, k in ipairs(self._kids) do t[i] = k end return t end
	function o:FindFirstChild(n) for _, k in ipairs(self._kids) do if k.Name == n then return k end end end
	function o:GetAttribute(n) return self._attr[n] end
	function o:add(k) self._kids[#self._kids + 1] = k; k.Parent = self; return k end
	return o
end

-- 5x5 heart-ish picture, row r = z index, col c = x index
local PIC = {
	"01010",
	"11111",
	"11111",
	"01110",
	"00100",
}
local N = 5
local function runs(bits)
	local out, n = {}, 0
	for i = 1, #bits do
		if bits[i] == 1 then n = n + 1 elseif n > 0 then out[#out + 1] = n; n = 0 end
	end
	if n > 0 then out[#out + 1] = n end
	if #out == 0 then out[1] = 0 end
	return out
end

local ws, serverData, lp, hrp, tilesByRC
local function clue(pos, nums)
	local p = inst("Clue", { Position = pos })
	local sg = p:add(inst("SurfaceGui"))
	for _, v in ipairs(nums) do
		local f = sg:add(inst("ClueNumberFrame"))
		f:add(inst("ClueNumberLabel", { Text = tostring(v) }))
	end
	return p
end

local function buildWorld(pic)
	if pic then PIC, N = pic, #pic end
	ws = inst("Workspace")
	local tiles = ws:add(inst("Tiles"))
	tilesByRC = {}
	for r = 1, N do
		tilesByRC[r] = {}
		for c = 1, N do
			local t = tiles:add(inst("Tile", { Position = V3(c * 5, 0, r * 5), Size = V3(5, 1, 5) }))
			tilesByRC[r][c] = t
		end
	end
	local normal = ws:add(inst("Clues")):add(inst("Normal"))
	for r = 1, N do
		local bits = {}
		for c = 1, N do bits[c] = tonumber(PIC[r]:sub(c, c)) end
		normal:add(clue(V3(-5, 0, r * 5), runs(bits)))   -- left of the board, first number nearest
	end
	for c = 1, N do
		local bits = {}
		for r = 1, N do bits[r] = tonumber(PIC[r]:sub(c, c)) end
		normal:add(clue(V3(c * 5, 0, -5), runs(bits)))
	end
	serverData = ws:add(inst("ServerData", { _attr = { State = "RoundActive" } }))
	ws.CurrentCamera = {
		CFrame = { Position = V3(15, 40, -10), LookVector = V3(0, -0.8, 0.6), RightVector = V3(-1, 0, 0), UpVector = V3(0, 0.6, 0.8) },
		ViewportSize = { X = 1920, Y = 1080 }, FieldOfView = 70,
	}
	hrp = inst("HumanoidRootPart", { Position = V3(15, 3, 15) })
	local ch = inst("Character"); ch:add(hrp)
	lp = inst("LocalPlayer", { Character = ch, _attr = { FillMode = -1, PlayingState = "InActiveRound" } })
end

local renderCb
local function installGlobals()
	workspace = ws
	local players = { LocalPlayer = lp }
	local rs = { RenderStepped = { Connect = function(_, f) renderCb = f; return { Disconnect = function() renderCb = nil end } end } }
	game = { GetService = function(_, n) return (n == "Players" and players) or (n == "RunService" and rs) or nil end }
	Drawing = { new = function() local o = {}; function o:Remove() end; return o end }
	WorldToScreen = function() return Vector2.new(0, 0), false end
	keypress, keyrelease = function() end, function() end
	iskeypressed = function() return false end
	isrbxactive = function() return true end
	notify = function() end
end

local realPrint = print
local quiet = true
local errs = {}
print = function(...)
	local line = table.concat({ ... }, " ")
	for _, w in ipairs({ "render: ", "state: ", "scan: ", "auto: ", "live view: ", "solver error" }) do
		if line:find("[nonogram] " .. w, 1, true) == 1 then errs[#errs + 1] = line end
	end
	if not quiet then realPrint(...) end
end

local function load()
	local f = assert(loadfile(SCRIPT))
	f()
	return _G.nonogram
end

local function frames(n, dt)
	for _ = 1, n do T = T + (dt or 0.016); if renderCb then renderCb() end end
end

------------------------------------------------------------------------------
-- tests
------------------------------------------------------------------------------
buildWorld()
installGlobals()
local S = load()
frames(200)

local B = S.board
check(B ~= nil, "board read")
check(S.status == "solved", "solved, got " .. tostring(S.status))
if B and B.res and B.res.sol then
	local ok = true
	for r = 1, N do for c = 1, N do
		if B.res.sol[r][c] ~= (PIC[r]:sub(c, c) == "1" and 1 or 2) then ok = false end
	end end
	check(ok, "solution matches the picture")
end

-- arm, then break the character lookup: errors must back off, not disarm
S.autofill(true)
local A = S.autoState
frames(5)
check(A.on, "armed")
isrbxactive = function() error("boom") end
frames(600, 0.05)
check(A.on, "still armed after repeated errors")
check(A.benched ~= nil, "sits out the board after repeated errors")
isrbxactive = function() return true end
check(#errs > 0, "the injected error was reported")
for i = #errs, 1, -1 do errs[i] = nil end

-- a new board clears the bench
serverData._attr.State = "Intermission"
frames(60, 0.05)
check(A.on, "armed through intermission")
serverData._attr.State = "RoundActive"
frames(120, 0.05)
check(S.board ~= nil and A.board == S.board, "picked up the new board")
check(A.benched == nil, "bench cleared on a new board")

-- two mistake timeouts: sit out, stay armed
for _ = 1, 2 do
	lp._attr.Timeout = 3; frames(20, 0.05)
	lp._attr.Timeout = 0; frames(20, 0.05)
end
check(A.on, "still armed after two mistakes")
check(A.benched == "two mistakes", "sits out after two mistakes, got " .. tostring(A.benched))

-- fill mode left on while benched gets switched off
lp._attr.FillMode = 1
local pressed = {}
keypress = function(vk) pressed[vk] = true; if vk == 0x51 then lp._attr.FillMode = -1 end end
frames(60, 0.05)
check(pressed[0x51] and lp._attr.FillMode == -1, "fill mode switched off while benched")

-- fill mode that never switches: keep retrying, stay armed
lp._attr.FillMode = 1
keypress = function() end
frames(2000, 0.05)
check(A.on, "still armed when fill mode won't switch")

-- re-running the script keeps it armed
lp._attr.FillMode = -1
S = load()
frames(5)
check(S.autoState.on, "re-run keeps auto fill armed")

-- F7 (autofill(false)) is what disarms
S.autofill(false)
frames(100, 0.05)
check(not S.autoState.on, "autofill(false) disarms")
S = load()
frames(5)
check(not S.autoState.on, "re-run after disarm stays off")
S.stop()

------------------------------------------------------------------------------
-- live solving view
------------------------------------------------------------------------------
buildWorld()
installGlobals()
S = load()
check(S.liveOn == true, "live view on by default")
frames(40) -- about 0.64 s
check(S.lv ~= nil, "live solve started when the board spawned")
check(S.status == "solved", "the answer doesn't wait for the live view")
local early = S.lv and S.lv.steps or 0
check(early >= 2 and early <= 20, "live solve is paced (steps after 0.6 s: " .. early .. ")")
local sawKinds, doneStatus = {}, nil
for _ = 1, 600 do
	frames(1)
	local L = S.lv
	if L and L.ev then
		sawKinds[L.ev.k] = true
		if L.ev.k == "d" then doneStatus = L.ev.status end
	end
end
check(sawKinds.r and sawKinds.c, "live view shows rows and columns being solved")
check(doneStatus == "unique", "live solve ends solved, got " .. tostring(doneStatus))
check(S.lv == nil, "live view clears after it finishes")

S.live(false)
check(not S.liveOn and S.lv == nil, "F6 turns the live view off")
S = load()
frames(5)
check(S.liveOn == false, "re-run keeps the live view off")
S.live(true)
check(S.lv ~= nil and S.lv.board == S.board, "turning it on solves the current board live")
S = load()
check(S.liveOn == true, "re-run keeps the live view on")
-- a new board restarts it
serverData._attr.State = "Intermission"; frames(20, 0.05)
check(S.lv == nil, "live view dropped with the board")
serverData._attr.State = "RoundActive"; frames(30, 0.05)
check(S.lv ~= nil and S.lv.board == S.board, "live view starts on the next board")
S.stop()

-- an ambiguous board (4x4, one tile per row and column): no line helps, so
-- the live view has to try tiles both ways and then guess
buildWorld({ "1000", "0100", "0010", "0001" })
installGlobals()
S = load()
local amb, ambDone = {}, nil
for _ = 1, 1500 do
	frames(1)
	local L = S.lv
	if L and L.ev then
		amb[L.ev.k] = true
		if L.ev.k == "d" then ambDone = L.ev.status end
	end
end
check(amb.t and amb.g and amb.f, "ambiguous board: live view shows trials, guesses and answers")
check(ambDone == "multiple", "ambiguous board: live solve ends ambiguous, got " .. tostring(ambDone))
check(S.status == "ambiguous", "ambiguous board: overlay status, got " .. tostring(S.status))
S.stop()
check(#errs == 0, "no errors reported by the script: " .. table.concat(errs, " | "))

-- the live view never shows a solid tile the answer disagrees with, even
-- when the round says the clues are reversed (the solver tries a wrong
-- reading first there)
local liveWrong, liveBoards = 0, 0
for seed = 1, 12 do
	math.randomseed(100 + seed)
	local n = math.random(6, 12)
	local pic = {}
	for r = 1, n do local row = {} for c = 1, n do row[c] = (math.random() < 0.6) and "1" or "0" end pic[r] = table.concat(row) end
	buildWorld(pic)
	serverData._attr.CurrentReversedCluesSetting = (seed % 2 == 0)
	installGlobals()
	S = load()
	for _ = 1, 3000 do
		frames(1)
		local L, B = S.lv, S.board
		if L and L.grid and B and B.res and B.res.sol then
			local g, sol = L.grid, B.res.sol
			for r = 1, B.R do for c = 1, B.C do
				if g[r][c] == 1 and sol[r][c] ~= 1 then liveWrong = liveWrong + 1 end
			end end
		end
		if B and B.res and not S.lv then break end
	end
	if S.board and S.board.res then liveBoards = liveBoards + 1 end
	S.stop()
end
check(liveBoards == 12, "live view boards solved")
check(liveWrong == 0, "live view never shows a wrong solid tile (" .. liveWrong .. " seen)")
check(#errs == 0, "no errors in the live view checks: " .. table.concat(errs, " | "))

-- playing a board: fill its tiles while the live view runs and F6 is
-- pressed. Re-solves must finish, the answer must stay right, and there is
-- never more than one solver coroutine alive (Matcha broke with two).
do
	local realCreate, alive, maxAlive = coroutine.create, {}, 0
	coroutine.create = function(f)
		local co = realCreate(f)
		alive[co] = true
		return co
	end
	local function countAlive()
		local n = 0
		for co in pairs(alive) do
			if coroutine.status(co) == "dead" then alive[co] = nil else n = n + 1 end
		end
		return n
	end
	local stuck, wrongAns = 0, 0
	for seed = 1, 4 do
		math.randomseed(200 + seed)
		local n = 12
		local pic = {}
		for r = 1, n do local row = {} for c = 1, n do row[c] = (math.random() < 0.55) and "1" or "0" end pic[r] = table.concat(row) end
		buildWorld(pic)
		installGlobals()
		S = load()
		local k = 0
		for r = 1, n do for c = 1, n do
			if pic[r]:sub(c, c) == "1" then
				local t = tilesByRC[r][c]
				t._attr.Solved, t._attr.Filled = true, true
				k = k + 1
				if k % 7 == 0 then S.live(false); frames(2); S.live(true) end
				for _ = 1, 3 do frames(1); maxAlive = math.max(maxAlive, countAlive()) end
			end
		end end
		for _ = 1, 400 do frames(1); maxAlive = math.max(maxAlive, countAlive()) end
		if S.status == "solving" then stuck = stuck + 1 end
		local B = S.board
		for _, t in ipairs(B.cells) do
			if t.want ~= ((pic[t.r]:sub(t.c, t.c) == "1") and 1 or 2) then wrongAns = wrongAns + 1 end
		end
		S.stop()
	end
	coroutine.create = realCreate
	check(maxAlive <= 1, "never more than one solver coroutine alive (saw " .. maxAlive .. ")")
	check(stuck == 0, "no board left stuck on solving")
	check(wrongAns == 0, "answers right after playing the board (" .. wrongAns .. " wrong tiles)")
	check(#errs == 0, "no errors while playing: " .. table.concat(errs, " | "))
end

-- auto fill plays boards that logic alone can't finish: it has to guess.
-- A tiny game: WASD walks (camera looks along +Z), F / Q switch fill mode,
-- standing on a tile in fill mode fills it, a wrong tile is a 2 s timeout.
local function playBoard(pic, limit)
	buildWorld(pic)
	installGlobals()
	local held, timeoutUntil, misses, gameT = {}, 0, 0, 0
	keypress = function(vk)
		held[vk] = true
		if vk == 0x46 and lp._attr.FillMode == -1 then lp._attr.FillMode = 1 end
		if vk == 0x51 and lp._attr.FillMode == 1 then lp._attr.FillMode = -1 end
	end
	keyrelease = function(vk) held[vk] = nil end
	local S = load()
	S.live(false)
	S.autofill(true)
	local function won()
		for r = 1, N do for c = 1, N do
			if PIC[r]:sub(c, c) == "1" and not tilesByRC[r][c]._attr.Filled then return false end
		end end
		return true
	end
	local dt = 1 / 60
	while gameT < limit and not won() do
		gameT = gameT + dt
		local dx, dz = 0, 0
		if held[0x57] then dz = dz + 1 end
		if held[0x53] then dz = dz - 1 end
		if held[0x44] then dx = dx - 1 end
		if held[0x41] then dx = dx + 1 end
		local m = math.sqrt(dx * dx + dz * dz)
		local p = hrp.Position
		if m > 0 then p = V3(p.X + dx / m * 16 * dt, p.Y, p.Z + dz / m * 16 * dt); hrp.Position = p end
		lp._attr.Timeout = (gameT < timeoutUntil) and (timeoutUntil - gameT) or 0
		local c, r = math.floor(p.X / 5 + 0.5), math.floor(p.Z / 5 + 0.5)
		local t = tilesByRC[r] and tilesByRC[r][c]
		if t and lp._attr.FillMode == 1 and gameT >= timeoutUntil and not t._attr.Solved
			and math.abs(p.X - c * 5) < 2.5 and math.abs(p.Z - r * 5) < 2.5 then
			if PIC[r]:sub(c, c) == "1" then
				t._attr.Solved, t._attr.Filled = true, true
			else
				timeoutUntil, misses = gameT + 2, misses + 1
			end
		end
		frames(1, dt)
	end
	local A = S.autoState
	local res = { won = won(), t = gameT, misses = misses, guesses = A.guesses or 0, wrong = A.misses or 0,
		on = A.on, benched = A.benched }
	S.stop()
	keypress, keyrelease = function() end, function() end
	return res
end

do
	-- one tile per row and column: no line ever helps, every fill is a guess
	local r1 = playBoard({ "00100", "10000", "00001", "01000", "00010" }, 240)
	check(r1.won, string.format("guessing finishes a board with no logic (%.0fs, %d guesses, %d wrong)", r1.t, r1.guesses, r1.wrong))
	check(r1.guesses > 0, "it guessed")
	check(r1.on and not r1.benched, "wrong guesses don't make it sit out the board")
	check(r1.misses == r1.wrong, "every timeout was a guess it knew was one (" .. r1.misses .. " timeouts, " .. r1.wrong .. " wrong guesses)")
	-- random boards whose clues allow more than one answer
	local wins, games = 0, 0
	for seed = 1, 5 do
		math.randomseed(300 + seed)
		local pic = {}
		for r = 1, 8 do local row = {} for c = 1, 8 do row[c] = (math.random() < 0.5) and "1" or "0" end pic[r] = table.concat(row) end
		local rr = playBoard(pic, 300)
		games = games + 1
		if rr.won and rr.misses == rr.wrong then wins = wins + 1 end
	end
	check(wins == games, "random ambiguous boards all finished (" .. wins .. "/" .. games .. ")")
	check(#errs == 0, "no errors while guessing: " .. table.concat(errs, " | "))
end

------------------------------------------------------------------------------
-- solver core, straight from the script
------------------------------------------------------------------------------
local src = io.open(SCRIPT):read("*a")
local coreSrc = src:match("%-%-%[%[<<CORE>>%]%](.-)%-%-%[%[<</CORE>>%]%]")
check(coreSrc ~= nil, "core section found")
local Core = assert(loadstring(coreSrc .. "\nreturn Core"))()

local function cluesOf(pic, R, C)
	local rows, cols = {}, {}
	for r = 1, R do local b = {} for c = 1, C do b[c] = pic[r][c] end rows[r] = { nums = runs(b) } end
	for c = 1, C do local b = {} for r = 1, R do b[r] = pic[r][c] end cols[c] = { nums = runs(b) } end
	return rows, cols
end
local function fitsClues(g, rows, cols, R, C)
	for r = 1, R do
		local b = {} for c = 1, C do b[c] = g[r][c] == 1 and 1 or 0 end
		if table.concat(runs(b), ",") ~= table.concat(rows[r].nums, ",") then return false end
	end
	for c = 1, C do
		local b = {} for r = 1, R do b[r] = g[r][c] == 1 and 1 or 0 end
		if table.concat(runs(b), ",") ~= table.concat(cols[c].nums, ",") then return false end
	end
	return true
end

math.randomseed(7)
local kinds, same, valid, fits, total = {}, true, true, true, 0
for _ = 1, 60 do
	local R, C = math.random(4, 10), math.random(4, 10)
	local pic = {}
	for r = 1, R do pic[r] = {} for c = 1, C do pic[r][c] = (math.random() < 0.5) and 1 or 0 end end
	local rows, cols = cluesOf(pic, R, C)
	local plain = Core.solve(rows, cols, R, C)
	rows, cols = cluesOf(pic, R, C) -- fresh clue tables (prepClue caches on them)
	Core.watch = function(ev)
		total = total + 1
		kinds[ev.k] = true
		for _, key in ipairs(ev.cells or {}) do
			local r, c = math.floor(key / 4096), key % 4096
			if not (ev.grid[r] and ev.grid[r][c] ~= 0) then valid = false end
		end
		if (ev.k == "r" or ev.k == "c" or ev.k == "p") and ev.grid ~= ev.base then valid = false end
	end
	local watched = Core.solve(rows, cols, R, C)
	Core.watch = nil
	if plain.status ~= watched.status then same = false end
	if plain.sol and watched.sol then
		for r = 1, R do for c = 1, C do if plain.sol[r][c] ~= watched.sol[r][c] then same = false end end end
		if not fitsClues(watched.sol, rows, cols, R, C) then fits = false end
	end
	if watched.status == "none" then fits = false end
end
check(same, "watching doesn't change the solver's answers")
check(valid, "every step's tiles are set in its grid")
check(fits, "every answer fits its clues")
for _, k in ipairs({ "r", "c", "t", "p", "g", "f" }) do
	check(kinds[k], "random puzzles produce '" .. k .. "' steps")
end

print = realPrint
print(string.format("%d passed, %d failed", passes, fails))
os.exit(fails == 0 and 0 or 1)

--[[
    Nonogram Helper  -  Matcha overlay
    place 96277935599613 (the walk-to-fill nonogram game)

    Reads workspace.Tiles and workspace.Clues, solves the puzzle and paints the
    answer on the board. Auto fill (F7) walks the character over the answer
    with real WASD input and toggles fill mode with the game's F / Q keys; it
    fires no remotes. Hands off the keyboard while it runs.

    Console API (after running):
        _G.nonogram.toggle()        show / hide the overlay
        _G.nonogram.autofill()      arm / disarm auto fill (same as F7)
        _G.nonogram.replay()        replay the solving process (same as F6)
        _G.nonogram.process(false)  stop replaying every new board's solve
        _G.nonogram.crosses(true)   also mark the tiles that must stay empty
        _G.nonogram.rescan()        re-read the board and solve again
        _G.nonogram.info()          print the current solve summary
        _G.nonogram.dump()          print the solution as ascii
        _G.nonogram.stop()          tear everything down
    F8 toggles the overlay, F7 arms / disarms auto fill (it stays armed across
    rounds), F6 replays how the current board was solved.

    Colours:  green  = fill this tile (walk over it in fill mode)
              yellow = fill, but only a best guess (clues are hidden or ambiguous)
              red x  = must stay empty (only with crosses on)
]]

local CFG = {
	togglekey = 0x77,   -- F8: overlay
	autokey   = 0x76,   -- F7: auto fill
	autoSprint = true,  -- hold shift while walking when the round allows sprinting
	autoGuesses = false, -- auto fill also steps on guessed tiles (costs lives when wrong)
	pace      = 0.1,    -- seconds between tile-state scan ticks
	budget    = 0.002,  -- seconds of attribute reads allowed per scan tick
	statePoll = 0.5,    -- seconds between round-state reads (ServerData attrs cost ~1ms)
	bigBoard  = 1000,   -- tiles; above this, listing the board costs ms, so it is cached
	bigBudget = 0.004,  -- read budget per scan tick on big boards
	guessShow = 40,     -- guesses are drawn only if there are at most this many
	                    -- (or 10% of the fills); past that they are one random pick of many
	render    = 0.025,  -- seconds between overlay reprojections (only while something moved)
	slice     = 0.006,  -- seconds of solving per frame
	inset     = 0.42,   -- fraction of the tile's half-width the marks cover
	fillAlpha = 0.45,
	crosses   = false,
	showProcess = true, -- replay how each new board gets solved
	replaykey = 0x75,   -- F6: replay the solving process
	playTime  = 8,      -- seconds a replay takes (steps are spread over it)
	playMin   = 0.003,  -- fastest step
	playMax   = 0.12,   -- slowest step
	playLive  = 0.02,   -- step pace while the solver is still running
	playHold  = 1.2,    -- seconds the last step stays up
}

local COL = {
	fill  = Color3.fromRGB(70, 220, 110),
	guess = Color3.fromRGB(235, 200, 60),
	empty = Color3.fromRGB(230, 70, 70),
	hud   = Color3.fromRGB(255, 255, 255),
	flash = Color3.fromRGB(255, 255, 255), -- tiles the current step proved
	hl    = Color3.fromRGB(110, 190, 255), -- outline of the line being solved
	probe = Color3.fromRGB(220, 120, 255), -- outline of a probed tile
}

------------------------------------------------------------------------------
-- teardown of a previous run (Drawing objects are not in the game tree)
------------------------------------------------------------------------------
local prev = _G.nonogram
_G.nonogram = nil
if prev then
	pcall(function() if prev._r then prev._r:Disconnect() end end)
	if prev.autoState then for vk in pairs(prev.autoState.held or {}) do pcall(keyrelease, vk) end end
	for _, o in ipairs(prev._draw or {}) do pcall(function() o:Remove() end) end
end

local function svc(n) return game:GetService(n) or game[n] end
local RunService = svc("RunService")
local Players = svc("Players")

--[[<<CORE>>]]
------------------------------------------------------------------------------
-- SOLVER CORE  -  pure lua, no roblox api, unit-testable offline
-- cells: 0 unknown, 1 filled, 2 empty
-- a clue is { nums = {..}, unordered = bool }; a number of -1 means hidden
-- (any length). A nil clue leaves its line unconstrained.
------------------------------------------------------------------------------
local Core = { pause = nil }

-- One arrangement of block lengths. Adds every feasible filled cell to diff
-- and every feasible empty cell to canE; returns false if nothing fits.
local function lineFit(line, lo, hi, k, n, pe, diff, canE)
	local function noEmpty(s, e) return pe[e] - pe[s - 1] == 0 end

	local f = {}
	for i = 0, n do f[i] = {} end
	f[0][0] = true
	for i = 1, n do
		local fi, fp = f[i], f[i - 1]
		local ce = line[i] ~= 1
		for j = 0, k do
			local ok = (fp[j] and ce) or false
			if not ok and j >= 1 then
				for L = lo[j], hi[j] do
					local s = i - L + 1
					if s < 1 or not noEmpty(s, i) then break end
					if s == 1 then
						if j == 1 then ok = true break end
					elseif line[s - 1] ~= 1 and s >= 2 and f[s - 2][j - 1] then
						ok = true break
					end
				end
			end
			if ok then fi[j] = true end
		end
	end
	if not f[n][k] then return false end

	local g = {}
	for i = 1, n + 2 do g[i] = {} end
	g[n + 1][k + 1] = true
	g[n + 2][k + 1] = true
	for i = n, 1, -1 do
		local gi, gn = g[i], g[i + 1]
		local ce = line[i] ~= 1
		for j = k + 1, 1, -1 do
			local ok = (gn[j] and ce) or false
			if not ok and j <= k then
				for L = lo[j], hi[j] do
					local e = i + L - 1
					if e > n or not noEmpty(i, e) then break end
					if e == n then
						if j == k then ok = true break end
					elseif line[e + 1] ~= 1 and g[e + 2][j + 1] then
						ok = true break
					end
				end
			end
			if ok then gi[j] = true end
		end
	end

	for c = 1, n do
		if line[c] ~= 1 and not canE[c] then
			for j = 0, k do
				if f[c - 1][j] and g[c + 1][j + 1] then canE[c] = true break end
			end
		end
	end
	for j = 1, k do
		for s = 1, n do
			local before
			if s == 1 then before = (j == 1)
			else before = line[s - 1] ~= 1 and s >= 2 and f[s - 2][j - 1] or false end
			if before then
				for L = lo[j], hi[j] do
					local e = s + L - 1
					if e > n or not noEmpty(s, e) then break end
					local after
					if e == n then after = (j == k)
					else after = line[e + 1] ~= 1 and g[e + 2][j + 1] or false end
					if after then diff[s] = diff[s] + 1; diff[e + 1] = diff[e + 1] - 1 end
				end
			end
		end
	end
	return true
end

-- Shuffled-clue lines: the numbers may sit in any order. A state is the set
-- of numbers already placed (a bitmask). Equal numbers are interchangeable,
-- so they are placed in index order: masks from the left keep earlier twins
-- first, masks from the right keep later twins, and the state count stays
-- small (at most 2^k, far fewer with repeats).
local function lineFitSet(line, lo, hi, k, n, pe, diff, canE)
	local function noEmpty(s, e) return pe[e] - pe[s - 1] == 0 end
	local pw, twinPrev = {}, {}
	for b = 1, k do
		pw[b] = 2 ^ (b - 1)
		for q = b - 1, 1, -1 do
			if lo[q] == lo[b] and hi[q] == hi[b] then twinPrev[b] = q break end
		end
	end
	local full = 2 ^ k - 1
	local function has(m, b) return math.floor(m / pw[b]) % 2 == 1 end

	-- A[p][m]: cells 1..p-1 settled holding exactly m, and a block may start at p
	local A = {}
	for p = 1, n + 1 do A[p] = {} end
	A[1][0] = true
	for p = 1, n do
		for m in pairs(A[p]) do
			if line[p] ~= 1 then A[p + 1][m] = true end
			for b = 1, k do
				if not has(m, b) and (not twinPrev[b] or has(m, twinPrev[b])) then
					for L = lo[b], hi[b] do
						local e = p + L - 1
						if e > n or not noEmpty(p, e) then break end
						if e == n or line[e + 1] ~= 1 then
							A[math.min(e + 2, n + 1)][m + pw[b]] = true
						end
					end
				end
			end
		end
	end
	if not A[n + 1][full] then return false end

	-- Bk[p][r]: cells p..n can hold exactly the set r, with a block free to start at p
	local Bk = {}
	for p = 1, n do Bk[p] = {} end
	local function back(p, r)
		if p > n then return r == 0 end
		local memo = Bk[p][r]
		if memo ~= nil then return memo end
		local ok = false
		if line[p] ~= 1 and back(p + 1, r) then ok = true end
		if not ok then
			for b = 1, k do
				if has(r, b) and (not twinPrev[b] or not has(r, twinPrev[b])) then
					for L = lo[b], hi[b] do
						local e = p + L - 1
						if e > n or not noEmpty(p, e) then break end
						if (e == n or line[e + 1] ~= 1) and back(math.min(e + 2, n + 1), r - pw[b]) then
							ok = true break
						end
					end
					if ok then break end
				end
			end
		end
		Bk[p][r] = ok
		return ok
	end

	for p = 1, n do
		for m in pairs(A[p]) do
			local rest = full - m
			if line[p] ~= 1 and not canE[p] and back(p + 1, rest) then canE[p] = true end
			for b = 1, k do
				if not has(m, b) and (not twinPrev[b] or has(m, twinPrev[b])) then
					for L = lo[b], hi[b] do
						local e = p + L - 1
						if e > n or not noEmpty(p, e) then break end
						if (e == n or line[e + 1] ~= 1) and back(math.min(e + 2, n + 1), rest - pw[b]) then
							diff[p] = diff[p] + 1; diff[e + 1] = diff[e + 1] - 1
							if e < n then canE[e + 1] = true end
						end
					end
				end
			end
		end
	end
	return true
end

-- lo/hi length bounds per number; a hidden number (-1) can be any length
local function prepClue(clue, n)
	if clue.arr then return clue.arr end
	local lo, hi = {}, {}
	for _, v in ipairs(clue.nums) do
		if v ~= 0 then
			if v < 0 then lo[#lo + 1], hi[#hi + 1] = 1, n
			else lo[#lo + 1], hi[#hi + 1] = v, v end
		end
	end
	clue.arr = { lo = lo, hi = hi, k = #lo, set = clue.unordered and #lo > 1 }
	return clue.arr
end
-- One line: returns the tightened line, or nil when the clue can't fit it.
local function solveLine(line, clue, n)
	if not clue then return line end
	local a = prepClue(clue, n)
	local pe = { [0] = 0 }
	for i = 1, n do pe[i] = pe[i - 1] + (line[i] == 2 and 1 or 0) end
	local diff, canE = {}, {}
	for i = 1, n + 1 do diff[i] = 0 end
	local fit = a.set and lineFitSet or lineFit
	if not fit(line, a.lo, a.hi, a.k, n, pe, diff, canE) then return nil end
	local out, run = {}, 0
	for c = 1, n do
		run = run + diff[c]
		local canF = run > 0
		if canF and canE[c] then out[c] = 0
		elseif canF then out[c] = 1
		elseif canE[c] then out[c] = 2
		else return nil end
		if line[c] ~= 0 and out[c] ~= line[c] then return nil end
	end
	return out
end
Core.solveLine = solveLine

local function copyGrid(g, R, C)
	local o = {}
	for r = 1, R do local row, src = {}, g[r]; for c = 1, C do row[c] = src[c] end; o[r] = row end
	return o
end
Core.copyGrid = copyGrid

-- Solve trace for the "solving process" replay: one step per line or probe
-- that proved cells. Only the main grid is recorded, never probe trials.
local function record(P, step)
	local tr = P.trace
	if not tr or tr.full then return end
	if #tr >= 40000 then tr.full = true return end
	tr[#tr + 1] = step
end

-- Runs line solving to a fixpoint. Returns false on a contradiction.
-- rec: this is the main grid, so proved cells go into the trace.
local function propagate(P, grid, dirtyR, dirtyC, rec)
	local R, C = P.R, P.C
	rec = rec and P.trace ~= nil
	local qR, qC, inR, inC = {}, {}, {}, {}
	for r = 1, R do if dirtyR == nil or dirtyR[r] then qR[#qR + 1] = r; inR[r] = true end end
	for c = 1, C do if dirtyC == nil or dirtyC[c] then qC[#qC + 1] = c; inC[c] = true end end
	local line = {}
	while #qR > 0 or #qC > 0 do
		if Core.pause then Core.pause() end
		P.lines = P.lines + 1
		if #qR > 0 then
			local r = table.remove(qR); inR[r] = nil
			local row = grid[r]
			for c = 1, C do line[c] = row[c] end
			local out = solveLine(line, P.rows[r], C)
			if not out then return false end
			local cells
			for c = 1, C do
				if row[c] == 0 and out[c] ~= 0 then
					row[c] = out[c]
					if rec then cells = cells or {}; cells[#cells + 1] = r; cells[#cells + 1] = c; cells[#cells + 1] = out[c] end
					if not inC[c] then inC[c] = true; qC[#qC + 1] = c end
				end
			end
			if cells then record(P, { k = "r", i = r, cells = cells }) end
			for c = 1, C do line[c] = nil end
		else
			local c = table.remove(qC); inC[c] = nil
			for r = 1, R do line[r] = grid[r][c] end
			local out = solveLine(line, P.cols[c], R)
			if not out then return false end
			local cells
			for r = 1, R do
				if grid[r][c] == 0 and out[r] ~= 0 then
					grid[r][c] = out[r]
					if rec then cells = cells or {}; cells[#cells + 1] = r; cells[#cells + 1] = c; cells[#cells + 1] = out[r] end
					if not inR[r] then inR[r] = true; qR[#qR + 1] = r end
				end
			end
			if cells then record(P, { k = "c", i = c, cells = cells }) end
			for r = 1, R do line[r] = nil end
		end
	end
	return true
end

local function firstUnknown(grid, R, C)
	for r = 1, R do
		local row = grid[r]
		for c = 1, C do if row[c] == 0 then return r, c end end
	end
end

-- Try each unknown cell both ways. A side that contradicts fixes the other;
-- when both sides hold, any cell they agree on is forced too. Stops quietly
-- once P.lines passes P.cap (fewer sure cells, never wrong ones).
local function probe(P, grid)
	local R, C = P.R, P.C
	local changed = true
	while changed do
		changed = false
		for r = 1, R do
			for c = 1, C do
				if P.lines > P.cap then return true end
				if grid[r][c] == 0 then
					local ok, tt = {}, {}
					for v = 1, 2 do
						local t = copyGrid(grid, R, C)
						t[r][c] = v
						ok[v] = propagate(P, t, { [r] = true }, { [c] = true })
						tt[v] = t
					end
					if not ok[1] and not ok[2] then return false end
					local dR, dC, cells = {}, {}, {}
					if ok[1] ~= ok[2] then
						grid[r][c] = ok[1] and 1 or 2
						dR[r], dC[c] = true, true
						cells[1], cells[2], cells[3] = r, c, grid[r][c]
					else
						local a, b = tt[1], tt[2]
						for rr = 1, R do
							local ra, rb, rg = a[rr], b[rr], grid[rr]
							for cc = 1, C do
								if rg[cc] == 0 and ra[cc] ~= 0 and ra[cc] == rb[cc] then
									rg[cc] = ra[cc]
									dR[rr], dC[cc] = true, true
									cells[#cells + 1] = rr; cells[#cells + 1] = cc; cells[#cells + 1] = ra[cc]
								end
							end
						end
					end
					if next(dR) then
						if P.trace then record(P, { k = "p", i = r, j = c, cells = cells }) end
						if not propagate(P, grid, dR, dC, true) then return false end
						changed = true
					end
				end
			end
		end
	end
	return true
end

local function search(P, grid, found, limit, budget)
	budget.n = budget.n - 1
	if P.lines > P.scap then budget.n = -1 end
	if budget.n < 0 then return end
	-- probing only pays off at the root (it decides the sure cells there);
	-- inside the search plain propagation is far cheaper per node
	if not propagate(P, grid) then return end
	local br, bc = firstUnknown(grid, P.R, P.C)
	if not br then found[#found + 1] = grid return end
	for v = 1, 2 do
		local t = copyGrid(grid, P.R, P.C)
		t[br][bc] = v
		search(P, t, found, limit, budget)
		if #found >= limit or budget.n < 0 then return end
	end
end

-- rows[r] / cols[c] are clues (or nil). given[r][c] seeds known cells.
-- Returns { sol = grid|nil, sure = grid|nil, status = "unique"|"multiple"|"none"|"gaveup" }
-- sure holds only cells that every solution shares (0 elsewhere); sol is one
-- full answer, missing when the search ran out of budget before finding one.
-- trace: optional table that collects the proving steps (see record)
function Core.solve(rows, cols, R, C, given, budget, cap, trace)
	local P = { rows = rows, cols = cols, R = R, C = C, lines = 0, cap = cap or 30000, trace = trace }
	local grid = {}
	for r = 1, R do
		grid[r] = {}
		for c = 1, C do grid[r][c] = (given and given[r] and given[r][c]) or 0 end
	end
	if not propagate(P, grid, nil, nil, true) then return { status = "none" } end
	if firstUnknown(grid, R, C) and not probe(P, grid) then return { status = "none" } end
	local root = copyGrid(grid, R, C)
	if not firstUnknown(grid, R, C) then return { sol = grid, sure = grid, status = "unique" } end
	-- the search only yields one full answer to show as guesses; with most of a
	-- big board still open that answer is one random pick of many, so skip it
	local open = 0
	for r = 1, R do for c = 1, C do if grid[r][c] == 0 then open = open + 1 end end end
	if open > 400 and open > R * C * 0.15 then return { sure = root, status = "gaveup" } end
	local found, b = {}, { n = budget or 3000 }
	P.scap = P.lines + 15000
	search(P, grid, found, 2, b)
	if #found == 0 then
		if b.n < 0 then return { sure = root, status = "gaveup" } end
		return { status = "none" }
	end
	local unique = #found == 1 and b.n >= 0
	if trace then
		-- whatever logic could not reach came from the search: one last step
		local cells, sol = {}, found[1]
		for r = 1, R do for c = 1, C do
			if root[r][c] == 0 then cells[#cells + 1] = r; cells[#cells + 1] = c; cells[#cells + 1] = sol[r][c] end
		end end
		record(P, { k = "s", cells = cells, guess = not unique })
	end
	if unique then return { sol = found[1], sure = found[1], status = "unique" } end
	return { sol = found[1], sure = root, status = (#found > 1) and "multiple" or "gaveup" }
end
--[[<</CORE>>]]

------------------------------------------------------------------------------
-- board reading
------------------------------------------------------------------------------
local S = {
	enabled = true, showCross = CFG.crosses, showProcess = CFG.showProcess, hl = {},
	board = nil,           -- see readBoard
	_draw = {}, tri = {}, ln = {}, hud = nil,
	tScan = 0, tState = 0, tRender = 0, tKey = 0,
	state = nil, status = "waiting for a round", rev = 0,
	dcol = {}, dvis = {}, said = {},
	co = nil, msPerTile = 0,
}
_G.nonogram = S

local function attr(inst, name)
	local ok, v = pcall(function() return inst:GetAttribute(name) end)
	if ok then return v end
end

-- sorted distinct values, merging anything within tol
local function cluster(vals, tol)
	table.sort(vals)
	local out = {}
	for _, v in ipairs(vals) do
		if #out == 0 or v - out[#out] > tol then out[#out + 1] = v end
	end
	return out
end

local function nearest(list, v, tol)
	local bi, bd = nil, tol
	for i, x in ipairs(list) do
		local d = math.abs(x - v)
		if d <= bd then bi, bd = i, d end
	end
	return bi
end

-- "?" or no digits means a hidden number
local function parseNum(text)
	if type(text) ~= "string" then return nil end
	local d = text:gsub("%D", "")
	if d ~= "" then return tonumber(d) end
	if text:find("?", 1, true) then return -1 end
	return nil
end

local function readClueNums(part)
	local sg = part:FindFirstChild("SurfaceGui")
	if not sg then return nil end
	local nums = {}
	for _, f in ipairs(sg:GetChildren()) do
		if f.Name == "ClueNumberFrame" then
			local lab = f:FindFirstChild("ClueNumberLabel")
			local v = lab and parseNum(lab.Text)
			if v then nums[#nums + 1] = v end
		end
	end
	-- no numbers yet usually means the part is still being built
	if #nums == 0 then return nil end
	return nums
end

-- Builds S.board from the live tree: tile geometry plus row/column clues.
-- Rows run along world X (one per Z), columns along world Z (one per X).
local function readBoard()
	local folder = workspace:FindFirstChild("Tiles")
	local cluesF = workspace:FindFirstChild("Clues")
	if not folder or not cluesF then return nil, "no board" end
	local list = folder:GetChildren()
	if #list == 0 then return nil, "no tiles" end

	local tiles, xsRaw, zsRaw = {}, {}, {}
	local half, top = nil, nil
	for i, t in ipairs(list) do
		local p = t.Position
		if p then
			tiles[#tiles + 1] = { li = i, x = p.X, z = p.Z }
			xsRaw[#xsRaw + 1] = p.X
			zsRaw[#zsRaw + 1] = p.Z
			if not half then
				local sz = t.Size
				half = sz and sz.X / 2 or 2.5
				top = p.Y + (sz and sz.Y / 2 or 0.5)
			end
		end
	end
	local tol = half * 0.5
	local xs, zs = cluster(xsRaw, tol), cluster(zsRaw, tol)
	local C, R = #xs, #zs
	if R * C ~= #list then return nil, string.format("tile grid %dx%d vs %d tiles", C, R, #list) end

	local B = { R = R, C = C, xs = xs, zs = zs, half = half, top = top, n = #list,
		cells = {}, at = {}, rows = {}, cols = {} }
	for _, t in ipairs(tiles) do
		local c, r = nearest(xs, t.x, tol), nearest(zs, t.z, tol)
		if not c or not r then return nil, "tile off grid" end
		t.r, t.c, t.state = r, c, 0
		B.cells[#B.cells + 1] = t
		B.at[r] = B.at[r] or {}
		B.at[r][c] = t
	end

	-- clue parts sit outside the grid: beyond X for rows, beyond Z for columns
	local minX, maxX, minZ, maxZ = xs[1], xs[C], zs[1], zs[R]
	local cx, cz = (minX + maxX) / 2, (minZ + maxZ) / 2
	local rowNums, colNums = { Normal = {}, Opposite = {} }, { Normal = {}, Opposite = {} }
	B.rowSide, B.colSide = -1, 1
	for _, side in ipairs({ "Normal", "Opposite" }) do
		local sf = cluesF:FindFirstChild(side)
		if sf then
			for _, part in ipairs(sf:GetChildren()) do
				local p = part.Position
				if p then
					if p.X < minX - half or p.X > maxX + half then
						local r = nearest(zs, p.Z, tol)
						if r then
							rowNums[side][r] = readClueNums(part)
							if side == "Normal" then B.rowSide = (p.X < cx) and -1 or 1 end
						end
					elseif p.Z < minZ - half or p.Z > maxZ + half then
						local c = nearest(xs, p.X, tol)
						if c then
							colNums[side][c] = readClueNums(part)
							if side == "Normal" then B.colSide = (p.Z < cz) and -1 or 1 end
						end
					end
				end
			end
		end
	end
	-- 50/50 rounds can show a line on only one side; merge both
	local missing = 0
	for r = 1, R do
		B.rows[r] = rowNums.Normal[r] or rowNums.Opposite[r]
		if not B.rows[r] then missing = missing + 1 end
	end
	for c = 1, C do
		B.cols[c] = colNums.Normal[c] or colNums.Opposite[c]
		if not B.cols[c] then missing = missing + 1 end
	end
	B.missing = missing

	local sd = workspace:FindFirstChild("ServerData")
	B.reversed = sd and attr(sd, "CurrentReversedCluesSetting") == true
	B.disordered = sd and attr(sd, "CurrentDisorderedCluesSetting") == true
	B.hidden = sd and attr(sd, "CurrentHiddenCluesSetting") == true
	return B
end

-- Clue lists read first-number-first from the Normal side. Returns clue
-- tables in grid order for one choice of reading direction.
local function orientClues(B, flipRows, flipCols)
	local rows, cols = {}, {}
	-- rows are indexed along ascending X; the first number sits at the Normal side
	local rowRev = (B.rowSide > 0) ~= (flipRows == true)
	local colRev = (B.colSide > 0) ~= (flipCols == true)
	local function mk(nums, rev)
		if not nums then return nil end
		local all = true
		for _, v in ipairs(nums) do if v >= 0 then all = false end end
		if #nums > 0 and all and #nums == 1 then return nil end -- a lone "?" says nothing
		local t = {}
		if rev then for i = #nums, 1, -1 do t[#t + 1] = nums[i] end
		else for i = 1, #nums do t[i] = nums[i] end end
		return { nums = t, unordered = B.disordered }
	end
	for r = 1, B.R do rows[r] = mk(B.rows[r], rowRev) end
	for c = 1, B.C do cols[c] = mk(B.cols[c], colRev) end
	return rows, cols
end

local function givens(B)
	local g, any = {}, false
	for r = 1, B.R do g[r] = {} end
	for _, t in ipairs(B.cells) do
		if t.state ~= 0 then g[t.r][t.c] = t.state; any = true end
	end
	return g, any
end

-- Solve every reading direction in turn (the Normal-side rule first) and keep
-- the first that fits the clues and every tile already filled or crossed.
local function solveBoard(B)
	local order = { { false, false }, { true, true }, { true, false }, { false, true } }
	if B.reversed then order = { { true, true }, { false, false }, { true, false }, { false, true } } end
	local g = givens(B)
	local prevRes = B.res
	if prevRes and prevRes.flip and prevRes.sure then
		-- re-solve: proven cells still hold, so start from them plus the new
		-- tiles; propagation then only has to chase what changed
		local seeded = givens(B)
		for r = 1, B.R do
			local sr, gr = prevRes.sure[r], seeded[r]
			for c = 1, B.C do
				if gr[c] == nil and sr[c] ~= 0 then gr[c] = sr[c] end
			end
		end
		local rows, cols = orientClues(B, prevRes.flip[1], prevRes.flip[2])
		local res = Core.solve(rows, cols, B.R, B.C, seeded, 3000, (B.n > CFG.bigBoard) and 1500 or 4000)
		res.flip = prevRes.flip
		if res.sol or res.sure then return res end
		-- a contradiction means the old answer was wrong: full solve below
	end
	local partial
	for _, o in ipairs(order) do
		local rows, cols = orientClues(B, o[1], o[2])
		local trace
		if B.wantTrace then
			trace = {}
			B.trace, B.traceStart, B.traceGen = trace, g, (B.traceGen or 0) + 1
		end
		local res = Core.solve(rows, cols, B.R, B.C, g, 3000, nil, trace)
		res.flip = o
		if res.sol then return res end
		-- ran out of budget without a contradiction: keep its proven cells
		-- unless another direction gives a full answer
		if res.sure and not partial then partial = res end
	end
	return partial or { status = "none" }
end

local function startSolve()
	local B = S.board
	if not B then return end
	S.status = "solving"
	S.co = coroutine.create(function() return solveBoard(B) end)
	S.coBoard = B
end

local function applyResult(B, res)
	B.res = res
	B.dirty = false
	local fill, guess = 0, 0
	local grid = res.sol or res.sure
	if grid then
		for _, t in ipairs(B.cells) do
			t.want = grid[t.r][t.c]
			t.sure = res.sure and res.sure[t.r][t.c] ~= 0
			if t.want == 1 then
				fill = fill + 1
				if not t.sure then guess = guess + 1 end
			end
		end
	end
	B.fillCount, B.guessCount = fill, guess
	B.showGuesses = guess <= math.max(CFG.guessShow, fill * 0.1)
	local names = { unique = "solved", multiple = "ambiguous", gaveup = "partial", none = "no solution" }
	S.status = names[res.status] or tostring(res.status)
end

local function stepSolve()
	local co = S.co
	if not co then return end
	local t0 = os.clock()
	Core.pause = function()
		if os.clock() - t0 > CFG.slice then coroutine.yield() end
	end
	local ok, res = coroutine.resume(co)
	Core.pause = nil
	if not ok then
		S.co = nil
		S.status = "solver error"
		print("[nonogram] solver error: " .. tostring(res))
		return
	end
	if coroutine.status(co) == "dead" then
		S.co = nil
		if S.board == S.coBoard and res then applyResult(S.board, res) end
	end
end

------------------------------------------------------------------------------
-- tile state scanning (Solved / Filled attributes, a few tiles per tick)
------------------------------------------------------------------------------
local function dropBoard(why)
	S.board, S.co = nil, nil
	S.status = why or "waiting for a round"
end

-- Tiles worth polling: everything still open, except that once the answer is
-- unique the must-stay-empty tiles only matter while their X marks are shown.
local function rebuildPending(B)
	local keep = {}
	local skipEmpty = B.res and B.res.status == "unique" and not S.showCross
	for i, t in ipairs(B.cells) do
		if t.state == 0 and not (skipEmpty and t.want == 2) then keep[#keep + 1] = i end
	end
	B.pending, B.cursor = keep, 1
end

local function buildBoard()
	local B, err = readBoard()
	if not B then S.status = err or "no board"; return false end
	rebuildPending(B)
	B.built = os.clock()
	B.wantTrace = true
	if S.showProcess then B.play = { gen = -1 } end -- starts once the trace does
	S.board = B
	startSolve()
	return true
end

local function rootPos()
	local lp = Players and Players.LocalPlayer
	local ch = lp and lp.Character
	local hrp = ch and ch:FindFirstChild("HumanoidRootPart")
	return hrp and hrp.Position
end

local function tickScan()
	local B = S.board
	if not B then return end
	local now = os.clock()
	local big = B.n > CFG.bigBoard
	local list = B.list
	-- small boards get a fresh listing every tick, so no handle outlives the
	-- tick that got it. Listing a big board costs ~13 ms (80x80), so there it
	-- is kept for a second; the round state is polled every 0.1 s instead and
	-- the board is dropped the moment the round stops.
	if not big or not list or now - (B.listAt or 0) > 1 then
		local folder = workspace:FindFirstChild("Tiles")
		if not folder then dropBoard("board gone"); return end
		list = folder:GetChildren()
		if #list ~= B.n then dropBoard("board changed"); return end
		B.list = big and list or nil
		B.listAt = now
	end
	local pend = B.pending
	if #pend == 0 then return end
	local t0 = os.clock()
	local done = 0
	-- one cheap identity check per tick: the listing order must still match
	local probeCell = B.cells[pend[((B.cursor - 1) % #pend) + 1]]
	local pt = list[probeCell.li]
	local pp = pt and pt.Position
	if not pp or math.abs(pp.X - probeCell.x) > 0.5 or math.abs(pp.Z - probeCell.z) > 0.5 then
		dropBoard("board changed"); return
	end
	local changed = false
	local function readCell(cell)
		if cell.state ~= 0 then return end
		done = done + 1
		local tile = list[cell.li]
		if tile and attr(tile, "Solved") then
			cell.state = attr(tile, "Filled") and 1 or 2
			changed = true
			if cell.want and cell.want ~= 0 and cell.want ~= cell.state then B.mismatch = true end
		end
	end
	-- the tiles around the player first, every tick, so your own fills clear fast
	local rp = rootPos()
	if rp then
		local pc = nearest(B.xs, rp.X, B.half * 1.2)
		local pr = nearest(B.zs, rp.Z, B.half * 1.2)
		if pc and pr then
			for r = pr - 1, pr + 1 do
				local row = B.at[r]
				if row then
					for c = pc - 1, pc + 1 do
						local cell = row[c]
						if cell then readCell(cell) end
					end
				end
			end
		end
	end
	-- then the rest of the board, round-robin, inside the read budget
	local budget = big and CFG.bigBudget or CFG.budget
	local i = B.cursor
	while i <= #pend and os.clock() - t0 < budget do
		readCell(B.cells[pend[i]])
		i = i + 1
	end
	if done > 0 then S.msPerTile = (os.clock() - t0) * 1000 / done end
	if i > #pend then
		rebuildPending(B)
	else
		B.cursor = i
	end
	if changed then B.dirty = true; S.rev = S.rev + 1 end
	-- re-solve when the board proves the answer wrong, or when new filled /
	-- crossed tiles could settle an ambiguous one
	if not S.co and B.dirty and (B.mismatch or (B.res and B.res.status ~= "unique")) then
		-- a big re-solve costs seconds, so it waits for more news
		if not B.tSolve or os.clock() - B.tSolve > (big and 5 or 1) then
			B.tSolve, B.mismatch, B.dirty = os.clock(), false, false
			startSolve()
		end
	end
end

local function tickState()
	local sd = workspace:FindFirstChild("ServerData")
	local st = sd and attr(sd, "State")
	local now = os.clock()
	if st ~= S.state then
		-- a fresh round gets a moment to finish building its tiles and clues;
		-- a script started mid-round (S.state nil) reads at once
		S.buildAt = (S.state == nil) and now or now + 0.75
		S.state, S.retries = st, 0
		if S.board then dropBoard() end
	end
	if st ~= "RoundActive" then
		if not S.board then S.status = "waiting for a round (" .. tostring(st) .. ")" end
		return
	end
	local B = S.board
	if not B then
		if now >= (S.buildAt or 0) then buildBoard() end
	elseif not S.co and (S.retries or 0) < 3 and now - B.built > 2
		and (B.missing > 0 or (B.res and B.res.status == "none")) then
		-- lines missing or no fit: the board was probably read half-built
		S.retries = (S.retries or 0) + 1
		dropBoard("re-reading")
		buildBoard()
	end
end

------------------------------------------------------------------------------
-- overlay
------------------------------------------------------------------------------
local function getTri(i)
	local o = S.tri[i]
	if not o then
		o = Drawing.new("Triangle")
		o.Filled, o.Transparency, o.Visible = true, CFG.fillAlpha, false
		S.tri[i] = o
		S._draw[#S._draw + 1] = o
	end
	return o
end

local function getLn(i)
	local o = S.ln[i]
	if not o then
		o = Drawing.new("Line")
		o.Thickness, o.Color, o.Transparency, o.Visible = 2, COL.empty, 0.8, false
		S.ln[i] = o
		S._draw[#S._draw + 1] = o
	end
	return o
end

-- only touch Color / Visible when they change. Drawing objects are userdata
-- that reject extra fields, so what was last written lives in S.dcol / S.dvis.
local function show(o, col)
	if col and S.dcol[o] ~= col then o.Color = col; S.dcol[o] = col end
	if not S.dvis[o] then o.Visible = true; S.dvis[o] = true end
end
local function hide(o)
	if S.dvis[o] then o.Visible = false; S.dvis[o] = false end
end

-- WorldToScreen returns (0, 0) for any point off screen, which stretched edge
-- tiles toward the corner. This projects with the camera itself (matches
-- WorldToScreen to 0.1 px on screen) and stays right off screen, so Drawing
-- just clips the part outside. Returns nil behind the camera; falls back to
-- WorldToScreen (on-screen points only) if the camera props are missing.
local function makeProjector(cam)
	local cf = cam and cam.CFrame
	local vp = cam and cam.ViewportSize
	local fov = cam and cam.FieldOfView
	if not (cf and vp and fov) then
		return function(x, y, z)
			local s, on = WorldToScreen(Vector3.new(x, y, z))
			if on then return s.X, s.Y end
		end, cf
	end
	local P, L, R, U = cf.Position, cf.LookVector, cf.RightVector, cf.UpVector
	local px, py, pz = P.X, P.Y, P.Z
	local lx, ly, lz, rx, ry, rz, ux, uy, uz = L.X, L.Y, L.Z, R.X, R.Y, R.Z, U.X, U.Y, U.Z
	local k = (vp.Y / 2) / math.tan(math.rad(fov) / 2)
	local cx, cy = vp.X / 2, vp.Y / 2
	return function(x, y, z)
		local dx, dy, dz = x - px, y - py, z - pz
		local d = dx * lx + dy * ly + dz * lz
		if d < 0.1 then return nil end
		return cx + (dx * rx + dy * ry + dz * rz) / d * k, cy - (dx * ux + dy * uy + dz * uz) / d * k
	end, cf, vp, fov
end

-- true when neither the camera nor anything drawn has changed since last time
local function unchanged(cf, vp, fov)
	if not cf then return false end
	local p, l = cf.Position, cf.LookVector
	local B = S.board
	local key = { p.X, p.Y, p.Z, l.X, l.Y, l.Z, vp and vp.X or 0, vp and vp.Y or 0, fov or 0,
		S.rev, S.status, B or false, B and B.res or false, S.enabled, S.showCross, S.autoTag or false }
	local old, same = S.drawnKey, true
	if not old then same = false
	else for i = 1, #key do if key[i] ~= old[i] then same = false break end end end
	S.drawnKey = key
	return same
end

------------------------------------------------------------------------------
-- solving process replay: the solver's proving steps played back on the
-- board. While a slow solve is still running it plays live behind it.
------------------------------------------------------------------------------
local function newPlay(B)
	local shown, guess = {}, {}
	local g = B.traceStart
	for r = 1, B.R do
		shown[r], guess[r] = {}, {}
		for c = 1, B.C do shown[r][c] = (g and g[r] and g[r][c]) or 0 end
	end
	return { i = 0, gen = B.traceGen, shown = shown, guess = guess, flash = {}, tNext = os.clock() }
end

local function tickPlay(now)
	local B = S.board
	local pl = B and B.play
	if not pl then return end
	-- a new trace (first solve, or another reading direction) restarts it
	if pl.gen ~= B.traceGen then
		if not B.trace then return end
		pl = newPlay(B)
		B.play = pl
		S.rev = S.rev + 1
	end
	local tr = B.trace
	local n = #tr
	local solving = S.co ~= nil and S.coBoard == B
	local delay = solving and CFG.playLive
		or math.max(CFG.playMin, math.min(CFG.playMax, CFG.playTime / math.max(n, 1)))
	if pl.tNext < now - 0.25 then pl.tNext = now end
	local moved, burst = false, 0
	while pl.i < n and now >= pl.tNext and burst < 400 do
		pl.i = pl.i + 1
		local st = tr[pl.i]
		local fl, cells = {}, st.cells
		for q = 1, #cells, 3 do
			local r, c = cells[q], cells[q + 1]
			pl.shown[r][c] = cells[q + 2]
			if st.guess then pl.guess[r][c] = true end
			fl[r * 4096 + c] = true
		end
		pl.flash, pl.cur = fl, st
		pl.tNext = pl.tNext + delay
		moved, burst = true, burst + 1
	end
	if moved then S.rev = S.rev + 1 end
	if pl.i >= n and not solving and B.res then
		if not pl.tEnd then
			pl.tEnd, pl.flash = now, {}
			S.rev = S.rev + 1
		elseif now - pl.tEnd > CFG.playHold then
			B.play = nil
			S.rev = S.rev + 1
		end
	end
end

local function stepText(B, pl)
	local n = B.trace and #B.trace or 0
	local head = string.format("solving process  step %d/%d%s", pl.i, n, (S.co and S.coBoard == B) and "+" or "")
	local st = pl.cur
	if not st then return head .. "   starting from the tiles already filled or crossed" end
	if pl.tEnd then return head .. "   done" end
	local cnt = #st.cells / 3
	local tiles = cnt == 1 and "tile" or "tiles"
	if st.k == "r" or st.k == "c" then
		local nums = (st.k == "r") and B.rows[st.i] or B.cols[st.i]
		local parts = {}
		for _, v in ipairs(nums or {}) do parts[#parts + 1] = (v < 0) and "?" or tostring(v) end
		return string.format("%s   %s [%s] proves %d %s", head, st.k == "r" and "row" or "column",
			table.concat(parts, " "), cnt, tiles)
	elseif st.k == "p" then
		return string.format("%s   no line helps: trying a tile both ways proves %d %s", head, cnt, tiles)
	end
	return string.format("%s   %s %d %s", head, st.guess and "logic ran out, guessing" or "a search settles the last", cnt, tiles)
end

-- outline around the row / column (or probed tile) of the current step
local function drawOutline(proj, B, pl, y)
	local st = pl and not pl.tEnd and pl.cur
	local hh = B and B.half or 0
	local x0, x1, z0, z1
	if st and st.k == "r" then
		x0, x1, z0, z1 = B.xs[1] - hh, B.xs[B.C] + hh, B.zs[st.i] - hh, B.zs[st.i] + hh
	elseif st and st.k == "c" then
		x0, x1, z0, z1 = B.xs[st.i] - hh, B.xs[st.i] + hh, B.zs[1] - hh, B.zs[B.R] + hh
	elseif st and st.k == "p" then
		x0, x1, z0, z1 = B.xs[st.j] - hh, B.xs[st.j] + hh, B.zs[st.i] - hh, B.zs[st.i] + hh
	end
	local pts
	if x0 then
		local ax, ay = proj(x0, y, z0)
		local bx, by = proj(x1, y, z0)
		local cx, cy = proj(x1, y, z1)
		local dx, dy = proj(x0, y, z1)
		if ax and bx and cx and dx then
			pts = { Vector2.new(ax, ay), Vector2.new(bx, by), Vector2.new(cx, cy), Vector2.new(dx, dy) }
		end
	end
	for k = 1, 4 do
		local o = S.hl[k]
		if not o then
			o = Drawing.new("Line")
			o.Thickness, o.Transparency, o.Visible = 3, 1, false
			S.hl[k] = o
			S._draw[#S._draw + 1] = o
		end
		if pts then
			o.From, o.To = pts[k], pts[k % 4 + 1]
			show(o, st.k == "p" and COL.probe or COL.hl)
		else
			hide(o)
		end
	end
end

local function render()
	local proj, cf, vp, fov = makeProjector(workspace.CurrentCamera)
	if unchanged(cf, vp, fov) then return end
	local t0 = os.clock()
	local nt, nl = 0, 0
	local B = S.board
	local pl = B and B.play
	if pl and pl.gen ~= B.traceGen then pl = nil end -- trace not started yet
	local y = B and B.top + 0.05
	if S.enabled and B and (pl or (B.res and (B.res.sol or B.res.sure))) then
		local h = B.half * CFG.inset * 2
		local vw, vh = vp and vp.X or 1e9, vp and vp.Y or 1e9
		local guesses = B.showGuesses
		-- a tile's size on screen, measured at the board centre: tiles whose
		-- centre is further than that outside the screen can't show, so their
		-- corners are never projected (80x80 has ~6000 of those)
		local mid = B.at[math.ceil(B.R / 2)][math.ceil(B.C / 2)]
		local m = 400
		local x1, y1 = proj(mid.x, y, mid.z)
		local x2, y2 = proj(mid.x + B.half * 2, y, mid.z + B.half * 2)
		if x1 and x2 then m = math.abs(x2 - x1) + math.abs(y2 - y1) + 8 end
		for _, t in ipairs(B.cells) do
			-- v: 1 draw a fill quad, 2 draw an X; col: its colour
			local v, col
			if t.state == 0 then
				if pl then
					local sv = pl.shown[t.r][t.c]
					if sv ~= 0 then
						v = sv
						if pl.flash[t.r * 4096 + t.c] then col = COL.flash
						elseif sv == 1 then col = pl.guess[t.r][t.c] and COL.guess or COL.fill
						else col = COL.empty end
					end
				elseif t.want == 1 and (t.sure or guesses) then
					v, col = 1, t.sure and COL.fill or COL.guess
				elseif S.showCross and t.want == 2 and t.sure then
					v, col = 2, COL.empty
				end
			end
			if v then
				local sx, sy = proj(t.x, y, t.z)
				if not (sx and sx > -m and sx < vw + m and sy > -m and sy < vh + m) then v = nil end
			end
			if v then
				local ax, ay = proj(t.x - h, y, t.z - h)
				local bx, by = proj(t.x + h, y, t.z - h)
				local cx, cy = proj(t.x + h, y, t.z + h)
				local dx, dy = proj(t.x - h, y, t.z + h)
				if ax and bx and cx and dx then
					local a, b, c, d = Vector2.new(ax, ay), Vector2.new(bx, by), Vector2.new(cx, cy), Vector2.new(dx, dy)
					if v == 1 then
						nt = nt + 1
						local t1 = getTri(nt)
						t1.PointA, t1.PointB, t1.PointC = a, b, c
						show(t1, col)
						nt = nt + 1
						local t2 = getTri(nt)
						t2.PointA, t2.PointB, t2.PointC = a, c, d
						show(t2, col)
					else
						nl = nl + 1
						local l1 = getLn(nl)
						l1.From, l1.To = a, c
						show(l1, col)
						nl = nl + 1
						local l2 = getLn(nl)
						l2.From, l2.To = b, d
						show(l2, col)
					end
				end
			end
		end
	end
	for i = nt + 1, #S.tri do hide(S.tri[i]) end
	for i = nl + 1, #S.ln do hide(S.ln[i]) end
	drawOutline(proj, B, S.enabled and pl or nil, y)

	local hud, hud2 = S.hud, S.hud2
	if not hud then
		hud = Drawing.new("Text")
		hud.Center, hud.Outline, hud.Size = false, true, 16
		hud.Color = COL.hud
		hud.Position = Vector2.new(12, 12)
		S.hud = hud
		S._draw[#S._draw + 1] = hud
		hud2 = Drawing.new("Text")
		hud2.Center, hud2.Outline, hud2.Size = false, true, 16
		hud2.Color = COL.hl
		hud2.Position = Vector2.new(12, 32)
		S.hud2 = hud2
		S._draw[#S._draw + 1] = hud2
	end
	if S.enabled then
		local txt
		if B and B.res and (B.res.sol or B.res.sure) then
			local left, unsure = 0, 0
			for _, t in ipairs(B.cells) do
				if t.want == 1 and t.state == 0 then
					if t.sure then left = left + 1 else unsure = unsure + 1 end
				end
			end
			txt = string.format("nonogram %dx%d  [%s]  sure fills left %d", B.C, B.R, S.status, left)
			if unsure > 0 then
				txt = txt .. string.format(B.showGuesses and "  guesses %d (yellow)" or "  unsure %d (not shown)", unsure)
			end
		elseif B then
			txt = string.format("nonogram %dx%d  [%s]", B.C, B.R, S.status)
		else
			txt = "nonogram  [" .. tostring(S.status) .. "]"
		end
		if S.autoTag then txt = txt .. "  |  auto: " .. S.autoTag end
		if hud.Text ~= txt then hud.Text = txt end
		show(hud)
		if pl then
			local t2 = stepText(B, pl)
			if hud2.Text ~= t2 then hud2.Text = t2 end
			show(hud2)
		else
			hide(hud2)
		end
	else
		hide(hud)
		hide(hud2)
	end
	S.renderMs = (S.renderMs or 0) * 0.9 + (os.clock() - t0) * 100
end
------------------------------------------------------------------------------
-- auto fill: walks the character over the answer with fill mode on.
-- Movement is real WASD input steered by the camera. Fill mode is switched
-- with the game's own keys: from off, F turns it on; from on, Q turns it off
-- (true for both the 3-way and the single switch). Fill mode is only ever on
-- while the character stands on answer tiles or tiles already filled, and it
-- is confirmed off before stepping onto anything else.
------------------------------------------------------------------------------
local VK = { W = 0x57, A = 0x41, S = 0x53, D = 0x44, Q = 0x51, F = 0x46, SHIFT = 0xA0 }
local DR, DC = { 1, -1, 0, 0 }, { 0, 0, 1, -1 }
local A = { on = false, held = {}, phase = "idle", tCtl = 0 }
S.autoState = A

local function akey(vk, down)
	if down then
		if not A.held[vk] then keypress(vk); A.held[vk] = true end
	elseif A.held[vk] then
		keyrelease(vk); A.held[vk] = nil
	end
end

local function releaseMove()
	akey(VK.W, false); akey(VK.A, false); akey(VK.S, false); akey(VK.D, false); akey(VK.SHIFT, false)
end

local function releaseAll()
	for vk in pairs(A.held) do keyrelease(vk) end
	A.held = {}
end

-- the root handle is read every control tick, so it never goes stale unseen
local function autoRoot()
	local h = A.hrp
	if h and h.Parent then return h end
	local lp = Players and Players.LocalPlayer
	local ch = lp and lp.Character
	h = ch and ch:FindFirstChild("HumanoidRootPart")
	A.hrp = h
	return h
end

local function fillMode()
	local lp = Players and Players.LocalPlayer
	return lp and attr(lp, "FillMode")
end

local function fillable(t) return t.want == 1 and (t.sure or CFG.autoGuesses) end
-- safe to stand on with fill mode on
local function onSafe(t) return t.state == 1 or (t.state == 0 and fillable(t)) end
-- "passed" = stood on with fill mode on; wait for the scanner to confirm
local function isTarget(t, now) return t.state == 0 and fillable(t) and not (t.passed and now - t.passed < 2.5) end
local function anyCell() return true end

local function cellAt(B, x, z)
	local c = nearest(B.xs, x, B.half)
	local r = nearest(B.zs, z, B.half)
	return r and c and B.at[r][c] or nil
end

local function nearestCell(B, x, z)
	local best, bd = nil, math.huge
	for _, t in ipairs(B.cells) do
		local d = (t.x - x) ^ 2 + (t.z - z) ^ 2
		if d < bd then best, bd = t, d end
	end
	return best
end

-- shortest 4-way path from `from` through cells passing `pass` to the
-- nearest cell passing `goal`; returns the cells after `from`
local function bfs(B, from, pass, goal)
	local prev, seen = {}, { [from] = true }
	local q, h = { from }, 1
	while h <= #q do
		local t = q[h]; h = h + 1
		if t ~= from and goal(t) then
			local path = {}
			while t ~= from do table.insert(path, 1, t); t = prev[t] end
			return path
		end
		for k = 1, 4 do
			local row = B.at[t.r + DR[k]]
			local n = row and row[t.c + DC[k]]
			if n and not seen[n] and pass(n) then seen[n] = true; prev[n] = t; q[#q + 1] = n end
		end
	end
end

-- keep only the cells where the path turns, plus the end
local function corners(from, path)
	local wps = {}
	local pr, pc, dr, dc = from.r, from.c, nil, nil
	for i, t in ipairs(path) do
		local ndr, ndc = t.r - pr, t.c - pc
		if dr and (ndr ~= dr or ndc ~= dc) then wps[#wps + 1] = path[i - 1] end
		dr, dc, pr, pc = ndr, ndc, t.r, t.c
	end
	wps[#wps + 1] = path[#path]
	return wps
end

-- world directions of W and D, the way Roblox's ControlModule maps them
local function camAxes()
	local cam = workspace.CurrentCamera
	local cf = cam and cam.CFrame
	if not cf then return nil end
	local l = cf.LookVector
	local fx, fz = l.X, l.Z
	local m = math.sqrt(fx * fx + fz * fz)
	if m < 0.02 then
		local rv = cf.RightVector
		fx, fz = rv.Z, -rv.X
		m = math.sqrt(fx * fx + fz * fz)
		if m < 0.02 then return nil end
	end
	fx, fz = fx / m, fz / m
	return fx, fz, -fz, fx
end

-- press the WASD combination closest to world direction (dx, dz)
local function steer(dx, dz, sprint)
	local fx, fz, rx, rz = camAxes()
	if not fx or (dx == 0 and dz == 0) then releaseMove() return end
	local a = dx * fx + dz * fz
	local b = dx * rx + dz * rz
	akey(VK.W, a > 0.38); akey(VK.S, a < -0.38)
	akey(VK.D, b > 0.38); akey(VK.A, b < -0.38)
	akey(VK.SHIFT, sprint)
end

-- disarm: only F7, or trouble that keeps coming back
local function autoStop(reason, quiet)
	releaseAll()
	A.on, A.phase, A.nextFn, A.hrp, A.lp, A.stopAt = false, "idle", nil, nil, nil, nil
	S.autoTag = nil
	if reason then
		print("[nonogram] auto fill: " .. reason)
		if not quiet then pcall(notify, reason, "nonogram auto fill", 4) end
	end
end

local function goPlan() A.phase = "plan" end

-- stay armed, hands off for a while, then look again
local function autoWait(sec, tag)
	releaseMove()
	A.phase, A.nextFn, A.waitUntil, A.tag = "wait", nil, os.clock() + sec, tag
end

local function startSwitch(want, thenFn)
	releaseMove()
	A.phase, A.want, A.tries, A.tapKey, A.tapDone, A.nextFn = "switch", want, 0, nil, nil, thenFn
end

local function startSettle(thenFn)
	releaseMove()
	A.phase, A.nextFn, A.tSettle = "settle", thenFn, os.clock()
end

local function startMove(wps, thenFn)
	A.wps, A.wi, A.axisX = wps, 1, nil
	A.phase, A.nextFn = "move", thenFn
	A.best, A.tBest = math.huge, os.clock()
end

-- leave fill mode off, then disarm. Only possible mid-round with focus; in
-- any waiting state the game already has it off (or it can't be switched),
-- so disarm at once. A 2 s failsafe in autoTick covers the rest.
local function autoFinish(reason)
	local active = S.board and S.state == "RoundActive" and isrbxactive() and not A.inTimeout and not A.away
	if A.mode == 1 and active then
		A.stopAt = os.clock()
		startSwitch(-1, function() autoStop(reason) end)
	else
		autoStop(reason)
	end
end

local function runNext()
	local fn = A.nextFn
	A.nextFn = nil
	if fn then fn() else goPlan() end
end

local function tickSwitch(now)
	if A.tapKey then
		-- hold each tap ~50 ms so the game registers it
		if now - A.tapAt >= 0.05 then akey(A.tapKey, false); A.tapKey = nil; A.tapDone = now end
		return
	end
	if A.tapDone and now - A.tapDone < 0.05 then return end
	if now - (A.tRead or 0) < 0.03 then return end
	A.tRead = now
	local m = fillMode()
	A.mode = m
	if m == nil then autoWait(1, "can't read the fill mode") return end
	if m == A.want then A.switchFails = 0; runNext() return end
	if A.tapDone and now - A.tapDone < 0.35 then return end
	if A.tries >= 4 then
		A.switchFails = (A.switchFails or 0) + 1
		if A.switchFails >= 3 then
			autoStop("could not switch fill mode (chat open, or Hold To Fill on?)")
		else
			autoWait(3, "fill mode didn't switch, retrying")
		end
		return
	end
	local k
	if m == -1 then k = (A.want == 1) and VK.F or VK.Q
	elseif m == 1 then k = (A.want == -1) and VK.Q or VK.F
	else k = (A.want == 1) and VK.Q or VK.F end
	A.tries = A.tries + 1
	akey(k, true)
	A.tapKey, A.tapAt = k, now
end

local function tickMove(now, p)
	local wp = A.wps[A.wi]
	if not wp then releaseMove(); runNext() return end
	local ex, ez = wp.x - p.X, wp.z - p.Z
	if A.axisX == nil then A.axisX = math.abs(ex) >= math.abs(ez) end
	local prim = A.axisX and ex or ez
	local lat = A.axisX and ez or ex
	local final = A.wi == #A.wps
	local lead = (A.speed or 0) * 0.03
	local tolP = final and 0.4 or 0.7
	if math.abs(prim) <= tolP + lead and math.abs(lat) <= 1.0 then
		if final then
			A.stuck = 0
			releaseMove()
			runNext()
		else
			A.wi, A.axisX = A.wi + 1, nil
			A.best, A.tBest = math.huge, now
		end
		return
	end
	local dist = math.abs(prim) + math.abs(lat)
	if dist < A.best - 0.3 then
		A.best, A.tBest = dist, now
	elseif now - A.tBest > 1.5 then
		-- no progress: something is in the way. Re-plan a few times, then
		-- back off; only a board that keeps blocking disarms it
		A.stuck = (A.stuck or 0) + 1
		releaseMove()
		if A.stuck >= 4 then
			A.stuck = 0
			A.stuckTotal = (A.stuckTotal or 0) + 1
			if A.stuckTotal >= 5 then autoStop("keeps getting stuck on this board") return end
			autoWait(2, "blocked, retrying")
			return
		end
		goPlan()
		return
	end
	local sp = (math.abs(prim) > tolP + lead) and (prim > 0 and 1 or -1) or 0
	local sl = (math.abs(lat) > 0.8) and (lat > 0 and 1 or -1) or 0
	local sprint = A.sprint and math.abs(prim) > 4
	if A.axisX then steer(sp, sl, sprint) else steer(sl, sp, sprint) end
end

local function tickPlan(now, p)
	local B = S.board
	if not (B and B.res and (B.res.sol or B.res.sure)) then A.tag = "waiting for the answer" return end
	local m = fillMode()
	A.mode = m
	if m == nil then autoWait(1, "can't read the fill mode") return end
	if m ~= -1 and m ~= 1 then startSwitch(-1) return end -- never walk in cross mode
	local cur = cellAt(B, p.X, p.Z)
	local left, waiting, unsure = 0, 0, 0
	for _, t in ipairs(B.cells) do
		if t.state == 0 and t.want == 1 then
			if not fillable(t) then unsure = unsure + 1
			elseif isTarget(t, now) then left = left + 1
			else waiting = waiting + 1 end
		end
	end
	A.left = left + waiting
	if left == 0 then
		if m == 1 then
			-- nothing to fill right now: fill mode off before anything else
			if cur and onSafe(cur) then startSettle(function() startSwitch(-1) end) else startSwitch(-1) end
			return
		end
		if waiting > 0 then autoWait(0.3, "checking the last tiles") return end
		local tag = unsure > 0 and "sure tiles done, waiting for more clues" or "board done, waiting for the next round"
		if A.doneSaid ~= tag then
			A.doneSaid = tag
			print("[nonogram] auto fill: " .. tag)
			pcall(notify, tag, "nonogram auto fill", 3)
		end
		autoWait(0.5, tag)
		return
	end
	A.doneSaid = nil
	if m == 1 then
		if not cur then
			-- between tiles (a group gap) with fill on: turn it off first
			startSwitch(-1)
			return
		end
		if not onSafe(cur) then startSwitch(-1) return end
		local path = bfs(B, cur, onSafe, function(t) return isTarget(t, now) end)
		if path then
			A.tag = string.format("filling (%d left)", A.left)
			startMove(corners(cur, path), goPlan)
		else
			-- nothing more reachable over safe tiles: fill off, then walk
			startSettle(function() startSwitch(-1) end)
		end
		return
	end
	-- fill mode is off: walk to the nearest tile that needs filling
	if not cur then
		local t = nearestCell(B, p.X, p.Z)
		if not t or (t.x - p.X) ^ 2 + (t.z - p.Z) ^ 2 > 100 then autoWait(1, "walk onto the board") return end
		startMove({ t }, goPlan)
		return
	end
	if isTarget(cur, now) then
		if math.abs(p.X - cur.x) < 1.3 and math.abs(p.Z - cur.z) < 1.3 then
			A.tag = string.format("filling (%d left)", A.left)
			startSettle(function()
				startSwitch(1, function()
					A.phase, A.tDwell = "dwell", os.clock()
				end)
			end)
		else
			startMove({ cur }, goPlan)
		end
		return
	end
	local path = bfs(B, cur, anyCell, function(t) return isTarget(t, now) end)
	if not path then autoWait(1, "no path to the remaining tiles") return end
	A.tag = string.format("walking (%d left)", A.left)
	startMove(corners(cur, path), goPlan)
end

-- a new board: fresh counters, and this round's rules
local function autoNewBoard(B)
	releaseAll()
	A.board, A.phase, A.nextFn = B, "plan", nil
	A.mistakes, A.stuck, A.stuckTotal, A.switchFails = 0, 0, 0, 0
	A.inTimeout, A.away, A.doneSaid, A.inCell = false, false, nil, nil
	A.hrp, A.lp, A.speed = nil, nil, 0
	local sd = workspace:FindFirstChild("ServerData")
	A.noWalk = sd and attr(sd, "CurrentDisableWalkSetting") == true
	A.sprint = CFG.autoSprint and sd and attr(sd, "CurrentSprinting") == true
end

local function autoTick()
	local now = os.clock()
	if A.stopAt and now - A.stopAt > 2 then autoStop("stopped") return end
	local B = S.board
	if B ~= A.board then autoNewBoard(B) end
	if not B or S.state ~= "RoundActive" then
		releaseAll()
		A.phase, A.tag = "plan", "waiting for the next round"
		S.autoTag = A.tag
		return
	end
	if A.noWalk then
		releaseAll()
		A.tag = "walking is disabled this round"
		S.autoTag = A.tag
		return
	end
	if not isrbxactive() then
		releaseMove()
		A.tag, A.tBest = "paused: click into Roblox", now
		S.autoTag = A.tag
		return
	end
	local h = autoRoot()
	if not h then releaseMove(); A.tag = "no character"; S.autoTag = A.tag; return end
	local p = h.Position
	if A.lp then
		local dt = now - A.lt
		if dt > 0 then
			local v = math.sqrt((p.X - A.lp.X) ^ 2 + (p.Z - A.lp.Z) ^ 2) / dt
			A.speed = (A.speed or 0) * 0.6 + v * 0.4
		end
	end
	A.lp, A.lt = p, now
	if now - (A.tGuard or 0) > 0.3 then
		A.tGuard = now
		local lp = Players and Players.LocalPlayer
		-- a mistake puts the player in a timeout: wait it out, but a second
		-- one on the same board means something is off, so disarm
		local to = lp and attr(lp, "Timeout")
		local inTo = type(to) == "number" and to > 0
		if inTo and not A.inTimeout then
			A.mistakes = (A.mistakes or 0) + 1
			if A.mistakes >= 2 then autoStop("two mistakes on this board, stopped") return end
		end
		A.inTimeout = inTo
		local ps = lp and attr(lp, "PlayingState")
		A.away = ps ~= nil and ps ~= "InActiveRound"
		if A.phase ~= "switch" then A.mode = fillMode() end
	end
	if A.inTimeout or A.away then
		releaseMove()
		A.phase = "plan"
		A.tag = A.inTimeout and "mistake timeout, waiting" or "not playing this round"
		S.autoTag = A.tag
		return
	end
	local cur = cellAt(B, p.X, p.Z)
	if A.mode == 1 and cur then
		if not onSafe(cur) and A.phase ~= "switch" then
			-- should never happen; if it does, fill mode goes off at once
			startSwitch(-1)
		elseif fillable(cur) and cur.state == 0 then
			-- the game raycasts at 30 Hz: ~70 ms on a tile is enough to fill it
			if A.inCell ~= cur then A.inCell, A.inSince = cur, now
			elseif now - A.inSince > 0.07 then cur.passed = now end
		end
	end
	local ph = A.phase
	if ph == "plan" then tickPlan(now, p)
	elseif ph == "move" then tickMove(now, p)
	elseif ph == "switch" then tickSwitch(now)
	elseif ph == "wait" then
		if now >= A.waitUntil then goPlan() end
	elseif ph == "settle" then
		if ((A.speed or 0) < 0.6 and now - A.tSettle > 0.06) or now - A.tSettle > 0.4 then runNext() end
	elseif ph == "dwell" then
		if now - A.tDwell > 0.12 then
			if cur and fillable(cur) then cur.passed = now end
			goPlan()
		end
	end
	S.autoTag = A.on and A.tag or nil
end

-- armed until F7: it waits out round ends, finished boards and timeouts
local function autoStart()
	A.on, A.tag, A.stopAt = true, "starting", nil
	A.board = false -- forces autoNewBoard on the first tick
	print("[nonogram] auto fill armed - hands off the keyboard while it walks; F7 disarms")
	pcall(notify, "armed - hands off the keyboard, F7 stops", "nonogram auto fill", 3)
end

S.autofill = function(b)
	if b == nil then b = not A.on end
	if b and not A.on then autoStart()
	elseif not b and A.on then autoFinish("stopped") end
end
------------------------------------------------------------------------------
-- main loop: everything on RenderStepped behind elapsed-time gates
------------------------------------------------------------------------------
local function report(where, e)
	local msg = "[nonogram] " .. where .. ": " .. tostring(e)
	if not S.said[msg] then S.said[msg] = true; print(msg) end
end

S._r = RunService.RenderStepped:Connect(function()
	local now = os.clock()
	if now - S.tState >= ((S.board and S.board.n > CFG.bigBoard) and 0.1 or CFG.statePoll) then
		S.tState = now
		local ok, e = pcall(tickState)
		if not ok then S.status = "state error"; report("state", e) end
	end
	if S.co then stepSolve() end
	if now - S.tScan >= CFG.pace then
		S.tScan = now
		local ok, e = pcall(tickScan)
		if not ok then dropBoard("scan error"); report("scan", e) end
	end
	if now - S.tRender >= ((S.board and S.board.n > CFG.bigBoard) and 0.05 or CFG.render) then
		S.tRender = now
		local okp, ep = pcall(tickPlay, now)
		if not okp then
			if S.board then S.board.play = nil end
			report("replay", ep)
		end
		local ok, e = pcall(render)
		if not ok then report("render", e) end
	end
	if A.on and now - A.tCtl >= 0.008 then
		A.tCtl = now
		local ok, e = pcall(autoTick)
		if not ok then autoStop("error, stopped"); report("auto", e) end
	end
	if now - S.tKey >= 0.05 then
		S.tKey = now
		local down = iskeypressed(CFG.togglekey)
		if down and not S.keyWas then S.enabled = not S.enabled end
		S.keyWas = down
		local ad = iskeypressed(CFG.autokey)
		if ad and not S.autoWas then S.autofill() end
		S.autoWas = ad
		local rd = iskeypressed(CFG.replaykey)
		if rd and not S.replayWas then S.replay() end
		S.replayWas = rd
	end
end)

------------------------------------------------------------------------------
-- console api
------------------------------------------------------------------------------
S.toggle = function() S.enabled = not S.enabled; print("[nonogram] overlay " .. (S.enabled and "on" or "off")) end
S.crosses = function(b)
	S.showCross = (b ~= false)
	if S.board then rebuildPending(S.board) end
	print("[nonogram] crosses " .. (S.showCross and "on" or "off"))
end
S.rescan = function() dropBoard("rescanning"); S.state = nil; S.tState = 0 end
-- replay how the current board was solved (F6)
S.replay = function()
	local B = S.board
	if not (B and B.trace) then print("[nonogram] nothing to replay yet") return end
	B.play = newPlay(B)
	S.rev = S.rev + 1
end
-- replay each new board's solve automatically (on by default)
S.process = function(b)
	S.showProcess = (b ~= false)
	print("[nonogram] solving process " .. (S.showProcess and "shown on new boards" or "off (F6 still replays)"))
end

S.info = function()
	local B = S.board
	if not B then print("[nonogram] " .. tostring(S.status)) return end
	local filled, crossed = 0, 0
	for _, t in ipairs(B.cells) do
		if t.state == 1 then filled = filled + 1 elseif t.state == 2 then crossed = crossed + 1 end
	end
	print(string.format("[nonogram] %dx%d  status %s  fill %d (guesses %d)  board: filled %d crossed %d pending %d",
		B.C, B.R, tostring(S.status), B.fillCount or 0, B.guessCount or 0, filled, crossed, #B.pending))
	print(string.format("[nonogram] missing clue lines %d  reversed %s  disordered %s  hidden %s",
		B.missing, tostring(B.reversed), tostring(B.disordered), tostring(B.hidden)))
	print(string.format("[nonogram] cost: %.2f ms per tile read, %.2f ms per overlay redraw", S.msPerTile, S.renderMs or 0))
	if B.res and B.res.flip then
		print(string.format("[nonogram] reading direction flips: rows %s cols %s", tostring(B.res.flip[1]), tostring(B.res.flip[2])))
	end
end

S.dump = function()
	local B = S.board
	if not (B and B.res and (B.res.sol or B.res.sure)) then print("[nonogram] no solution yet") return end
	-- print from the Normal column-clue side down, Normal row-clue side on the left
	local rs, re, rstep = 1, B.R, 1
	if B.colSide > 0 then rs, re, rstep = B.R, 1, -1 end
	local cs, ce, cstep = 1, B.C, 1
	if B.rowSide > 0 then cs, ce, cstep = B.C, 1, -1 end
	for r = rs, re, rstep do
		local s = {}
		for c = cs, ce, cstep do
			local t = B.at[r][c]
			if t.state == 1 then s[#s + 1] = "#"
			elseif t.want == 1 then s[#s + 1] = t.sure and "o" or "?"
			else s[#s + 1] = "." end
		end
		print(table.concat(s))
	end
	print("  # filled on the board   o fill this   ? guessed fill   . empty")
end

S.stop = function()
	local me = S
	_G.nonogram = nil
	pcall(function() if me._r then me._r:Disconnect() end end)
	releaseAll()
	for _, o in ipairs(me._draw or {}) do pcall(function() o:Remove() end) end
	print("[nonogram] stopped")
end

print("[nonogram] running. F8 overlay, F7 auto fill, F6 replay the solve   _G.nonogram.info() / .dump() / .autofill() / .replay() / .stop()")

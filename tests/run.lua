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

local function buildWorld()
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
print = function(...) if not quiet then realPrint(...) end end

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

print = realPrint
print(string.format("%d passed, %d failed", passes, fails))
os.exit(fails == 0 and 0 or 1)

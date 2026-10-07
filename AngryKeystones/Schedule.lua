local ADDON, Addon = ...
local Mod = Addon:NewModule('Schedule')

local rowCount = 4
local PARTY_PREFIX = 'AK_KEYS'
local REQUEST = 'R'
local RESPONSE = 'K'
local CHAT_REQUEST_COOLDOWN = 5 * 60
local lastOwnPartyChatRequest = 0
local REQUEST_COOLDOWN = 30 * 60
local msPerWeek = 7 * 24 * 60 * 60
local GUILD_WINDOW_WIDTH = 330
local GUILD_WINDOW_HEIGHT = 350
local GUILD_WINDOW_MAX_WIDTH = 480
local PARTY_RESPONSE_TIMEOUT = 4
local PARTY_MIN_NAME_WIDTH = 70
local PARTY_MIN_KEY_WIDTH = 120
local PARTY_BEST_WIDTH = 44
local PARTY_MIN_WIDTH = 320
local PARTY_MAX_WIDTH = 390

-- Rotation harvested from napnapnapnap/mythic.pl.us (gh-pages/index.html).
-- Local Angry Keystones IDs: 1 Overflowing, 2 Skittish, 3 Volcanic,
-- 4 Necrotic, 5 Teeming, 6 Raging, 7 Bolstering, 8 Sanguine,
-- 9 Tyrannical, 10 Fortified.
local affixSchedule = {
	{ 6, 4, 10 }, -- wk1: Raging / Necrotic / Fortified
	{ 7, 1, 9 },  -- wk2: Bolstering / Overflowing / Tyrannical
	{ 8, 3, 10 }, -- wk3: Sanguine / Volcanic / Fortified
	{ 5, 4, 9 },  -- wk4: Teeming / Necrotic / Tyrannical
	{ 6, 3, 9 },  -- wk5: Raging / Volcanic / Tyrannical
	{ 7, 2, 10 }, -- wk6: Bolstering / Skittish / Fortified
	{ 8, 1, 9 },  -- wk7: Sanguine / Overflowing / Tyrannical
	{ 5, 2, 10 }, -- wk8: Teeming / Skittish / Fortified
}

-- Fixed reset epoch matching mythic.pl.us/getaffixes.js.
local epoch = 1789542000 -- 2026-09-16 07:00:00 UTC

local currentWeek
local requestKeystoneCheck
local partyKeys = {}
local ownKeystone
local lastPartyRequest = 0
local lastOwnKeyBroadcast = 0
local chatRequestCooldowns = {}
local lastGuildRequest = 0
local guildCache = {}
local guildCacheTime = 0
local guildWindow
local guildRows = {}
local guildScroll
local guildScrollChild
local guildRefreshButton
local guildStatus
local guildWindowOpen = false
local partyRequestStarted = 0
local keyChangeHighlightUntil = 0
local previousKeySignature
local weeklyBest = 0
local weeklyBestWeek
local minimapButton
local MINIMAP_KEYSTONE_ITEM_ID = 138019
local MINIMAP_BUTTON_RADIUS = 80

-- Forward declaration: party request timeout callbacks can run before the
-- function body is reached during file loading.
local UpdatePartyRows

local function GetRotationWeek()
	local weeksDiff = math.floor((time() - epoch) / msPerWeek)
	local index = (1 + (weeksDiff % #affixSchedule) + #affixSchedule) % #affixSchedule
	return index + 1
end

local function GetCurrentWeekStart()
	local weeksDiff = math.floor((time() - epoch) / msPerWeek)
	return epoch + weeksDiff * msPerWeek
end

local function GetPlayerName()
	return UnitName('player') or 'player'
end

local function GetFullPlayerName()
	local name, realm = UnitName('player')
	return name .. (realm and realm ~= '' and '-' .. realm or '')
end

local function GetKeySignature(key)
	if not key or not key.mapID or key.mapID == 0 or not key.level or key.level == 0 then
		return '0:0'
	end
	return key.mapID .. ':' .. key.level
end

local function GetKeyLevelColor(level)
	if not level or level <= 0 then
		return 0.7, 0.7, 0.7
	elseif level >= 7 then
		return 1.0, 0.50, 0.10 -- third affix active
	elseif level >= 4 then
		return 0.25, 0.80, 1.0 -- second affix active
	else
		return 0.65, 0.65, 0.65 -- first affix tier
	end
end

local function GetIlvlColor(ilvl)
	ilvl = tonumber(ilvl) or 0
	-- Legion gear uses blue/rare quality through roughly the low 830s and
	-- purple/epic quality from 835 onward. This is an approximation because
	-- addon messages carry the equipped average ilvl, not each item's quality.
	if ilvl >= 835 then
		return GetItemQualityColor(4) -- Epic / purple
	elseif ilvl >= 800 then
		return GetItemQualityColor(3) -- Rare / blue
	elseif ilvl > 0 then
		return GetItemQualityColor(2) -- Uncommon / green
	end
	return 1, 1, 1
end

local function RGBHex(r, g, b)
	r = math.floor((r or 1) * 255 + 0.5)
	g = math.floor((g or 1) * 255 + 0.5)
	b = math.floor((b or 1) * 255 + 0.5)
	return format('%02x%02x%02x', r, g, b)
end

local function SetPlayerLabel(row, name, class, ilvl)
	name = name or ''
	ilvl = tonumber(ilvl) or 0
	local r, g, b = 1, 1, 1
	if class then r, g, b = GetClassColor(class) end
	local text = '|cff' .. RGBHex(r, g, b) .. name .. '|r'
	if ilvl > 0 then
		local ir, ig, ib = GetIlvlColor(ilvl)
		text = text .. ' |cff' .. RGBHex(ir, ig, ib) .. tostring(ilvl) .. '|r'
	end
	row.Text:SetText(text)
	row.Text:SetTextColor(1, 1, 1)
	if row.IlvlBracket then row.IlvlBracket:Hide() end
	if row.Ilvl then row.Ilvl:Hide() end
	if row.IlvlClose then row.IlvlClose:Hide() end
end

local function FindBestKeystone()
	local best
	for container = BACKPACK_CONTAINER, NUM_BAG_SLOTS do
		local slots = GetContainerNumSlots(container)
		for slot = 1, slots do
			local _, _, _, _, _, _, slotLink = GetContainerItemInfo(container, slot)
			if slotLink then
				local itemString = slotLink:match('|Hkeystone:([0-9:]+)|h')
				if itemString then
					local info = { strsplit(':', itemString) }
					local mapID = tonumber(info[1])
					local level = tonumber(info[2])
					if mapID and level and (not best or level > best.level) then
						best = { mapID = mapID, level = level, link = slotLink }
					end
				end
			end
		end
	end
	return best
end

local function ResolveKeystoneMapName(key)
	if not key then return nil end
	if key.mapName and key.mapName ~= '' then return key.mapName end
	if C_ChallengeMode and C_ChallengeMode.GetMapInfo and key.mapID then
		local mapName = C_ChallengeMode.GetMapInfo(key.mapID)
		if type(mapName) == 'string' and mapName ~= '' then
			return mapName
		elseif type(mapName) == 'table' then
			return mapName.name or mapName.mapName
		end
	end
	-- Fallback: Legion keystone item links contain the localized dungeon
	-- name in their displayed item name even on clients without the map API.
	if key.link then
		local display = key.link:match('|h%[(.-)%]|h')
		if display then
			display = display:gsub('^Mythic Keystone:%s*', '')
			display = display:gsub('^Keystone:%s*', '')
			if display ~= '' then return display end
		end
	end
	return nil
end

local function GetKeystoneText(key)
	if not key then return 'No keystone' end
	local mapName = ResolveKeystoneMapName(key) or 'Unknown dungeon'
	return format('+%d %s', key.level, mapName)
end

local function GetWeeklyBestFromChallengeFrame()
	local best = 0
	if not ChallengesFrame or not ChallengesFrame.DungeonIcons then return nil end

	-- This is the Legion/Tauri source that is already visibly populated by the
	-- Blizzard Mythic Dungeons UI. Do not replace it with modern C_MythicPlus
	-- APIs: those are not the same data source on this client.
	for i = 1, #ChallengesFrame.DungeonIcons do
		local icon = ChallengesFrame.DungeonIcons[i]
		if icon and icon.IsShown and icon:IsShown() and icon.HighestLevel and icon.HighestLevel.GetText then
			local level = tonumber(icon.HighestLevel:GetText())
			if level and level > best then best = level end
		end
	end

	if best > 0 then return best end
	return nil
end

local function LoadWeeklyBest()
	local detected = GetWeeklyBestFromChallengeFrame()
	if detected then weeklyBest = detected end
	if not AngryKeystones_Data then AngryKeystones_Data = {} end
	if not AngryKeystones_Data.weeklyBest then AngryKeystones_Data.weeklyBest = {} end

	local key = GetFullPlayerName()
	local record = AngryKeystones_Data.weeklyBest[key]
	local weekStart = GetCurrentWeekStart()
	if record and record.week == weekStart then
		weeklyBest = math.max(weeklyBest or 0, tonumber(record.level) or 0)
		weeklyBestWeek = weekStart
	else
		weeklyBestWeek = weekStart
	end
end

local function SaveWeeklyBest(level)
	level = tonumber(level)
	if not level or level <= 0 then return end
	local weekStart = GetCurrentWeekStart()
	if weeklyBestWeek ~= weekStart then
		weeklyBest = 0
		weeklyBestWeek = weekStart
	end
	if level > weeklyBest then
		weeklyBest = level
		if not AngryKeystones_Data then AngryKeystones_Data = {} end
		if not AngryKeystones_Data.weeklyBest then AngryKeystones_Data.weeklyBest = {} end
		AngryKeystones_Data.weeklyBest[GetFullPlayerName()] = { week = weekStart, level = level }
	end
end

local function RefreshOwnKeystone()
	local oldSignature = previousKeySignature
	ownKeystone = FindBestKeystone()
	if ownKeystone and C_ChallengeMode and C_ChallengeMode.GetMapInfo then
		ownKeystone.mapName = C_ChallengeMode.GetMapInfo(ownKeystone.mapID)
	end
	local newSignature = GetKeySignature(ownKeystone)
	previousKeySignature = newSignature
	if oldSignature and oldSignature ~= newSignature then
		keyChangeHighlightUntil = GetTime() + 7
		if ownKeystone then ownKeystone.changedUntil = keyChangeHighlightUntil end
	elseif ownKeystone then
		ownKeystone.changedUntil = nil
	end
end

local function SendOwnKeystone(force, requestID, channel)
	if not ownKeystone then
		RefreshOwnKeystone()
	end

	local now = time()
	if not force and now - lastOwnKeyBroadcast < 1 then
		return
	end
	lastOwnKeyBroadcast = now

	local detectedWeeklyBest = GetWeeklyBestFromChallengeFrame()
	if detectedWeeklyBest then
		SaveWeeklyBest(detectedWeeklyBest)
	end
	if ownKeystone then
		ownKeystone.mapName = ResolveKeystoneMapName(ownKeystone)
	end
	local mapID = ownKeystone and ownKeystone.mapID or 0
	local level = ownKeystone and ownKeystone.level or 0
	local best = weeklyBest or 0
	local class = select(2, UnitClass('player')) or ''
	local name = GetFullPlayerName()
	local mapName = ownKeystone and ownKeystone.mapName or ''
	local ilvl = 0
	if GetAverageItemLevel then
		local _, equipped = GetAverageItemLevel()
		ilvl = math.floor((equipped or 0) + 0.5)
	end
	local specID, specName, specDescription, specIcon
	if GetSpecialization and GetSpecializationInfo then
		local specIndex = GetSpecialization()
		if specIndex then
			specID, specName, specDescription, specIcon = GetSpecializationInfo(specIndex)
		end
	end
	if type(specIcon) == 'number' then specIcon = tostring(specIcon) end
	if mapName == '' and ownKeystone then
		mapName = ResolveKeystoneMapName(ownKeystone) or ''
	end
	local message = RESPONSE .. ':' .. (requestID or '0') .. ':' .. mapID .. ':' .. level .. ':' .. best .. ':' .. class .. ':' .. name .. ':' .. mapName .. ':' .. ilvl .. ':' .. (specID or 0) .. ':' .. (specName or '') .. ':' .. (specIcon or '')
	SendAddonMessage(PARTY_PREFIX, message, channel or 'PARTY')
end

local function IsRegularParty()
	return IsInGroup() and not (IsInRaid and IsInRaid())
end

local function RequestPartyKeys()
	if not IsRegularParty() then
		partyKeys = {}
		return
	end

	local now = time()
	if now - lastPartyRequest < 2 then return end
	lastPartyRequest = now

	partyKeys = {}
	partyRequestStarted = GetTime()
	SendAddonMessage(PARTY_PREFIX, REQUEST .. ':PARTY', 'PARTY')
	SendOwnKeystone(true, 'PARTY', 'PARTY')
	if C_Timer and C_Timer.After then
		C_Timer.After(PARTY_RESPONSE_TIMEOUT, function()
			if partyRequestStarted > 0 and GetTime() - partyRequestStarted >= PARTY_RESPONSE_TIMEOUT then
				UpdatePartyRows()
			end
		end)
	end
end

local function UpdatePartyLayout()
	if not Mod.PartyFrame or not Mod.PartyFrame.Entries then return end
	local party = Mod.PartyFrame
	local contentLeft = 10
	local nameWidth = PARTY_MIN_NAME_WIDTH
	local keyWidth = PARTY_MIN_KEY_WIDTH
	for i = 1, #party.Entries do
		local row = party.Entries[i]
		if row:IsShown() then
			local nw = row.Text:GetStringWidth() or 0
			local kw = row.Key:GetStringWidth() or 0
			if nw + 4 > nameWidth then nameWidth = nw + 4 end
			if kw > keyWidth then keyWidth = kw end
		end
	end
	nameWidth = math.min(math.ceil(nameWidth + 4), 130)
	keyWidth = math.min(math.ceil(keyWidth + 8), 190)
	local width = math.max(PARTY_MIN_WIDTH, contentLeft + nameWidth + 8 + keyWidth + 8 + PARTY_BEST_WIDTH + 10)
	width = math.min(PARTY_MAX_WIDTH + 35, width)
	local available = width - contentLeft - nameWidth - 8 - 8 - PARTY_BEST_WIDTH - 10
	if available < PARTY_MIN_KEY_WIDTH then
		keyWidth = PARTY_MIN_KEY_WIDTH
		width = math.min(PARTY_MAX_WIDTH + 35, contentLeft + nameWidth + 8 + keyWidth + 8 + PARTY_BEST_WIDTH + 10)
	else
		keyWidth = math.min(keyWidth, available)
	end
	party:SetWidth(width)
	party.NameColumnWidth = nameWidth
	party.KeyColumnX = contentLeft + nameWidth + 8
	party.KeyColumnWidth = keyWidth
	party.BestColumnX = party.KeyColumnX + keyWidth + 8

	-- Headers and row data all use the party frame itself as their coordinate
	-- system. This avoids the tiny offsets caused by anchoring some elements
	-- to the decorative divider texture and others to the row frame.
	party.HeaderPlayer:ClearAllPoints()
	party.HeaderPlayer:SetPoint('TOPLEFT', party, 'TOPLEFT', contentLeft, -31)
	party.HeaderKey:ClearAllPoints()
	party.HeaderKey:SetPoint('TOPLEFT', party, 'TOPLEFT', party.KeyColumnX, -31)
	party.HeaderBest:ClearAllPoints()
	party.HeaderBest:SetPoint('TOPLEFT', party, 'TOPLEFT', party.BestColumnX, -31)
	party.HeaderBest:SetWidth(PARTY_BEST_WIDTH)
	party.HeaderBest:SetJustifyH('LEFT')

	for i = 1, #party.Entries do
		local row = party.Entries[i]
		row.Text:ClearAllPoints()
		row:SetPoint('TOPLEFT', party, 'TOPLEFT', contentLeft, -48 - ((i - 1) * 18))
		row.Text:SetPoint('LEFT', row, 'LEFT', 0, 0)
		row.Text:SetWidth(math.max(1, nameWidth))
		row.Key:ClearAllPoints()
		row.Key:SetPoint('LEFT', row, 'LEFT', party.KeyColumnX - contentLeft, 0)
		row.Key:SetWidth(keyWidth)
		row.Best:ClearAllPoints()
		row.Best:SetPoint('LEFT', row, 'LEFT', party.BestColumnX - contentLeft, 0)
		row.Best:SetWidth(PARTY_BEST_WIDTH)
		row.Best:SetJustifyH('LEFT')
	end
	if party.Empty then
		party.Empty:ClearAllPoints()
		party.Empty:SetPoint('TOPLEFT', party, 'TOPLEFT', contentLeft, -76)
		party.Empty:SetPoint('TOPRIGHT', party, 'TOPRIGHT', -10, -76)
	end
	if Mod.Container and Mod.Frame then
		Mod.Container:SetWidth(206 + 4 + width)
	end
end

local function SetPartyRow(row, name, class, key, ilvl)
	SetPlayerLabel(row, name, class, ilvl)

	if key then
		if key.mapID and key.mapID > 0 and key.level and key.level > 0 then
			row.Key:SetText(GetKeystoneText(key))
			row.Key:SetTextColor(GetKeyLevelColor(key.level))
		else
			row.Key:SetText(key.status or 'No keystone')
			row.Key:SetTextColor(0.7, 0.7, 0.7)
		end
	else
		row.Key:SetText('Waiting...')
		row.Key:SetTextColor(0.7, 0.7, 0.7)
	end

	if row.Best then
		local best = key and tonumber(key.weeklyBest) or 0
		if best > 0 then
			row.Best:SetText('+' .. best)
			row.Best:SetTextColor(GetKeyLevelColor(best))
		else
			row.Best:SetText('—')
			row.Best:SetTextColor(0.6, 0.6, 0.6)
		end
	end

	if key and key.changedUntil and key.changedUntil > GetTime() then
		row.Highlight:SetAlpha(0.22)
		row.Highlight:Show()
	else
		row.Highlight:Hide()
	end
end

UpdatePartyRows = function()
	if not Mod.PartyFrame then return end
	local shown = 0

	-- Party Keys is strictly for normal 5-player groups. In a raid, show only
	-- the player's own key and never expose raid members or stale party data.
	if IsInRaid and IsInRaid() then
		partyKeys = {}
		partyRequestStarted = 0
		for i = 2, 5 do
			Mod.PartyFrame.Entries[i]:Hide()
		end
		local row = Mod.PartyFrame.Entries[1]
		local name = UnitName('player') or 'You'
		local _, class = UnitClass('player')
		local key = ownKeystone
		if key then key.weeklyBest = weeklyBest or 0 end
		local ilvl = 0
		if GetAverageItemLevel then
			local _, equipped = GetAverageItemLevel()
			ilvl = math.floor((equipped or 0) + 0.5)
		end
		SetPartyRow(row, name, class, key or { mapID = 0, level = 0 }, ilvl)
		row:Show()
		Mod.PartyFrame.Empty:Show()
		UpdatePartyLayout()
		return
	end

	do
		local row = Mod.PartyFrame.Entries[1]
		local name = UnitName('player') or 'You'
		local _, class = UnitClass('player')
		local key = ownKeystone
		if key then key.weeklyBest = weeklyBest or 0 end
		local ilvl = 0
		if GetAverageItemLevel then
			local _, equipped = GetAverageItemLevel()
			ilvl = math.floor((equipped or 0) + 0.5)
		end
		SetPartyRow(row, name, class, key or { mapID = 0, level = 0 }, ilvl)
		row:Show()
		shown = shown + 1
	end

	for i = 1, 4 do
		local unit = 'party' .. i
		local row = Mod.PartyFrame.Entries[i + 1]
		if UnitExists(unit) then
			shown = shown + 1
			local name = GetUnitName(unit, true) or GetUnitName(unit) or ('Party ' .. i)
			local shortName = name:match('^([^%-]+)') or name
			local _, class = UnitClass(unit)
			local key = partyKeys[name] or partyKeys[shortName]
			if not key and partyRequestStarted > 0 and GetTime() - partyRequestStarted >= PARTY_RESPONSE_TIMEOUT then
				if UnitIsConnected and not UnitIsConnected(unit) then
					key = { mapID = 0, level = 0, status = 'Offline' }
				else
					key = { mapID = 0, level = 0, status = 'No addon' }
				end
			end
			SetPartyRow(row, shortName, class, key, key and key.ilvl or 0)
			row:Show()
		else
			row:Hide()
		end
	end
	Mod.PartyFrame.Empty:SetShown(shown == 1)
	UpdatePartyLayout()
end

local function UpdateAffixes()
	local detectedWeeklyBest = GetWeeklyBestFromChallengeFrame()
	if detectedWeeklyBest then
		SaveWeeklyBest(detectedWeeklyBest)
	end
	if ownKeystone then
		ownKeystone.mapName = ResolveKeystoneMapName(ownKeystone)
	end
	if requestKeystoneCheck then Mod:CheckInventoryKeystone() end
	if not ownKeystone then RefreshOwnKeystone() end
	if not currentWeek then currentWeek = GetRotationWeek() end

	for i = 1, rowCount do
		local entry = Mod.Frame.Entries[i]
		entry:Show()
		local scheduleWeek = (currentWeek + i - 3) % (#affixSchedule) + 1
		local affixes = affixSchedule[scheduleWeek]
		for j = 1, 3 do
			local affix = entry.Affixes[j]
			if affixes[j] then
				affix:SetUp(affixes[j])
				affix:Show()
			else affix:Hide() end
		end
	end
	Mod.Frame.Label:Hide()
	UpdatePartyRows()
	if Mod.GuildButton then Mod.GuildButton:SetShown(IsInGuild()) end
end

local function makeAffix(parent)
	local frame = CreateFrame('Frame', nil, parent)
	frame:SetSize(16, 16)
	local border = frame:CreateTexture(nil, 'OVERLAY')
	border:SetAllPoints()
	border:SetAtlas('ChallengeMode-AffixRing-Sm')
	frame.Border = border
	local portrait = frame:CreateTexture(nil, 'ARTWORK')
	portrait:SetSize(14, 14)
	portrait:SetPoint('CENTER', border)
	frame.Portrait = portrait
	frame.SetUp = ScenarioChallengeModeAffixMixin.SetUp
	frame:SetScript('OnEnter', ScenarioChallengeModeAffixMixin.OnEnter)
	frame:SetScript('OnLeave', GameTooltip_Hide)
	return frame
end

local function makePanel(parent, width, titleText)
	local frame = CreateFrame('Frame', nil, parent)
	frame:SetSize(width, 110)
	local bg = frame:CreateTexture(nil, 'BACKGROUND')
	bg:SetAllPoints()
	bg:SetAtlas('ChallengeMode-guild-background')
	bg:SetAlpha(0.4)
	local title = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormalMed2')
	title:SetText(titleText)
	title:SetPoint('TOPLEFT', 15, -7)
	frame.Title = title
	local line = frame:CreateTexture(nil, 'ARTWORK')
	line:SetSize(width - 14, 9)
	line:SetAtlas('ChallengeMode-RankLineDivider', false)
	line:SetPoint('TOP', 0, -20)
	frame.Line = line
	return frame
end

local function HideGuildWindow()
	if guildWindow then guildWindow:Hide() end
end

local function GetGuildRequestCooldown()
	local remaining = REQUEST_COOLDOWN - (time() - lastGuildRequest)
	if remaining < 0 then remaining = 0 end
	return remaining
end

local function SetGuildStatus()
	if not guildRefreshButton then return end
	local cooldown = GetGuildRequestCooldown()
	-- Keep the button mouse-active so its tooltip still works while cooling down.
	local texture = guildRefreshButton:GetNormalTexture()
	if texture and texture.SetDesaturated then texture:SetDesaturated(cooldown > 0) end
	guildRefreshButton:SetAlpha(cooldown > 0 and 0.55 or 1)
	local highlight = guildRefreshButton:GetHighlightTexture()
	if highlight and highlight.SetDesaturated then highlight:SetDesaturated(cooldown > 0) end
end

local function UpdateGuildLayout(entries)
	if not guildWindow or not guildScroll then return end
	local GUILD_SCROLL_LEFT = 14
	local nameWidth = 160
	local keyWidth = 120
	for i = 1, #entries do
		local row = guildRows[i]
		if row and row:IsShown() then
			local nw = row.Text:GetStringWidth() or 0
			local kw = row.Key:GetStringWidth() or 0
			if nw + 4 > nameWidth then nameWidth = nw + 4 end
			if kw > keyWidth then keyWidth = kw end
		end
	end
	nameWidth = math.min(math.ceil(nameWidth + 4), 210)
	keyWidth = math.min(math.ceil(keyWidth + 8), 230)
	local bestWidth = 42
	local playerTextX = 38
	local keyX = playerTextX + nameWidth + 10
	local bestX = keyX + keyWidth + 10
	local width = math.max(GUILD_WINDOW_WIDTH, bestX + bestWidth + 14)
	width = math.min(GUILD_WINDOW_MAX_WIDTH, width)
	local availableKey = width - keyX - 10 - bestWidth - 14
	if availableKey < 120 then availableKey = 120 end
	keyWidth = math.min(keyWidth, availableKey)
	bestX = keyX + keyWidth + 10
	width = math.max(GUILD_WINDOW_WIDTH, bestX + bestWidth + 14)
	width = math.min(GUILD_WINDOW_MAX_WIDTH, width)

	guildWindow:SetWidth(width)
	guildWindow.HeaderPlayer:ClearAllPoints()
	guildWindow.HeaderPlayer:SetPoint('TOPLEFT', guildWindow, 'TOPLEFT', playerTextX, -38)
	guildWindow.HeaderKey:ClearAllPoints()
	guildWindow.HeaderKey:SetPoint('TOPLEFT', guildWindow, 'TOPLEFT', keyX, -38)
	guildWindow.HeaderBest:ClearAllPoints()
	guildWindow.HeaderBest:SetPoint('TOPLEFT', guildWindow, 'TOPLEFT', bestX, -38)
	guildWindow.HeaderBest:SetWidth(bestWidth)
	guildWindow.HeaderBest:SetJustifyH('LEFT')
	guildScrollChild:SetWidth(width - 48)
	for i = 1, #guildRows do
		local row = guildRows[i]
		row.NameButton:SetWidth(math.max(1, nameWidth - 22))
		row.Text:SetWidth(math.max(1, nameWidth - 22))
		row.Key:ClearAllPoints()
		row.Key:SetPoint('LEFT', row, 'LEFT', keyX - GUILD_SCROLL_LEFT, 0)
		row.Key:SetWidth(keyWidth)
		row.Key:SetJustifyH('LEFT')
		row.Best:ClearAllPoints()
		row.Best:SetPoint('LEFT', row, 'LEFT', bestX - GUILD_SCROLL_LEFT, 0)
		row.Best:SetWidth(bestWidth)
		row.Best:SetJustifyH('LEFT')
	end
end

local function UpdateGuildRows()
	if not guildWindow then return end
	local entries = {}
	for name, data in pairs(guildCache) do
		entries[#entries + 1] = { name = name, data = data }
	end
	table.sort(entries, function(a, b) return a.name:lower() < b.name:lower() end)

	for i = 1, #entries do
		local row = guildRows[i]
		if not row then
			row = CreateFrame('Frame', nil, guildScrollChild)
			row:SetHeight(24)
			-- Textures do not support mouse scripts on the Legion client.
			-- Use a tiny button as the hover target and put the spec texture on it.
			row.SpecIcon = CreateFrame('Button', nil, row)
			row.SpecIcon:SetSize(18, 18)
			row.SpecIcon:SetPoint('LEFT', 2, 0)
			row.SpecIcon.Texture = row.SpecIcon:CreateTexture(nil, 'ARTWORK')
			row.SpecIcon.Texture:SetAllPoints()
			row.SpecIcon:Hide()
			row.SpecIcon:SetScript('OnEnter', function(self)
				if self.specName and self.specName ~= '' then
					GameTooltip:SetOwner(self, 'ANCHOR_RIGHT')
					GameTooltip:SetText(self.specName)
					GameTooltip:Show()
				end
			end)
			row.SpecIcon:SetScript('OnLeave', GameTooltip_Hide)
			row.NameButton = CreateFrame('Button', nil, row)
			row.NameButton:SetPoint('LEFT', row.SpecIcon, 'RIGHT', 4, 0)
			row.NameButton:SetSize(142, 20)
			row.Text = row.NameButton:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
			row.Text:SetPoint('LEFT', row.NameButton, 'LEFT', 0, 0)
			row.Text:SetWidth(100)
			row.Text:SetJustifyH('LEFT')
			row.Text:SetWordWrap(false)

			row.NameButton:SetScript('OnClick', function(self)
				if self.playerName and self.playerName ~= '' then
					ChatFrame_OpenChat('/w ' .. self.playerName .. ' ', DEFAULT_CHAT_FRAME)
				end
			end)
			row.NameButton:SetScript('OnEnter', function(self)
				if self.playerName and self.playerName ~= '' then
					GameTooltip:SetOwner(self, 'ANCHOR_CURSOR')
					GameTooltip:SetText('Whisper ' .. self.playerName)
					GameTooltip:Show()
				end
			end)
			row.NameButton:SetScript('OnLeave', GameTooltip_Hide)
			row.Key = row:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
			row.Key:SetPoint('LEFT', row.NameButton, 'RIGHT', 4, 0)
			row.Key:SetWidth(150)
			row.Key:SetJustifyH('LEFT')
			row.Best = row:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
			row.Best:SetPoint('RIGHT', -4, 0)
			row.Best:SetWidth(70)
			row.Best:SetJustifyH('RIGHT')
			guildRows[i] = row
		end

		local entry = entries[i]
		local data = entry.data
		row:SetPoint('TOPLEFT', 0, -(i - 1) * 24)
		row:SetWidth(guildScroll:GetWidth() - 18)
		row.NameButton.playerName = entry.name
		SetPlayerLabel(row, entry.name, data.class, data.ilvl)
		if data.specIcon and data.specIcon ~= '' then
			local icon = tonumber(data.specIcon) or data.specIcon
			row.SpecIcon.Texture:SetTexture(icon)
			row.SpecIcon.specName = data.specName or ''
			row.SpecIcon:Show()
		else
			row.SpecIcon:Hide()
			row.SpecIcon.specName = nil
		end
		if data.mapID and data.mapID > 0 and data.level and data.level > 0 then
			row.Key:SetText(GetKeystoneText(data))
			row.Key:SetTextColor(GetKeyLevelColor(data.level))
		else
			row.Key:SetText('No keystone')
			row.Key:SetTextColor(0.7, 0.7, 0.7)
		end
		if data.weeklyBest and data.weeklyBest > 0 then
			row.Best:SetText('+' .. data.weeklyBest)
			row.Best:SetTextColor(GetKeyLevelColor(data.weeklyBest))
		else
			row.Best:SetText('—')
			row.Best:SetTextColor(0.6, 0.6, 0.6)
		end
		row:Show()
	end
	for i = #entries + 1, #guildRows do guildRows[i]:Hide() end
	guildScrollChild:SetHeight(math.max(1, #entries * 24))
	UpdateGuildLayout(entries)
	SetGuildStatus()
end

local function CreateGuildWindow()
	if guildWindow then return end
	local frame = CreateFrame('Frame', ADDON .. 'GuildKeysWindow', UIParent)
	local frameHeight = (ChallengesFrame and ChallengesFrame.GetHeight and ChallengesFrame:GetHeight()) or GUILD_WINDOW_HEIGHT
	frame:SetSize(GUILD_WINDOW_WIDTH, frameHeight)
	frame:SetFrameStrata('DIALOG')
	frame:SetClampedToScreen(true)
	frame:EnableMouse(true)
	if ChallengesFrame then
		frame:SetPoint('TOPLEFT', ChallengesFrame, 'TOPRIGHT', 8, 0)
	end

	local bg = frame:CreateTexture(nil, 'BACKGROUND')
	bg:SetAllPoints()
	local backdropSource = ChallengesFrame
	if (not backdropSource or not backdropSource.GetBackdrop or not backdropSource:GetBackdrop()) and PVEFrame then
		backdropSource = PVEFrame
	end
	local usedParentBackdrop = false
	if backdropSource and backdropSource.GetBackdrop and frame.SetBackdrop then
		local parentBackdrop = backdropSource:GetBackdrop()
		if parentBackdrop then
			frame:SetBackdrop(parentBackdrop)
			if backdropSource.GetBackdropColor then
				local r, g, b, a = backdropSource:GetBackdropColor()
				frame:SetBackdropColor(r, g, b, a)
			end
			if backdropSource.GetBackdropBorderColor then
				local r, g, b, a = backdropSource:GetBackdropBorderColor()
				frame:SetBackdropBorderColor(r, g, b, a)
			end
			usedParentBackdrop = true
		end
	end
	if not usedParentBackdrop then
		bg:SetAtlas('ChallengeMode-guild-background')
		-- ElvUI skins the Mythic Dungeon background considerably more transparently
		-- than the stock Challenges UI. Match that visual only when ElvUI is present.
		if _G.ElvUI or _G.ElvUIParent then
			bg:SetAlpha(0.55)
		else
			bg:SetAlpha(0.95)
		end
	end

	local title = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormalLarge')
	title:SetPoint('TOPLEFT', 14, -10)
	title:SetText('Guild Keystones')
	frame.Title = title
	local close = CreateFrame('Button', nil, frame, 'UIPanelCloseButton')
	close:SetPoint('TOPRIGHT', 2, 2)
	close:SetScript('OnClick', function() Mod:HideGuildKeys(true) end)

	guildRefreshButton = CreateFrame('Button', nil, frame)
	guildRefreshButton:SetSize(24, 24)
	guildRefreshButton:SetPoint('LEFT', title, 'RIGHT', 6, 0)
	guildRefreshButton:SetNormalTexture('Interface\\Buttons\\UI-RefreshButton')
	guildRefreshButton:SetPushedTexture('Interface\\Buttons\\UI-RefreshButton')
	guildRefreshButton:SetHighlightTexture('Interface\\Buttons\\UI-RefreshButton')
	guildRefreshButton:SetScript('OnClick', function()
		if GetGuildRequestCooldown() <= 0 then Mod:RequestGuildKeys(true) end
	end)
	guildRefreshButton:SetScript('OnEnter', function(self)
		GameTooltip:SetOwner(self, 'ANCHOR_TOP')
		local cooldown = GetGuildRequestCooldown()
		GameTooltip:SetText('Refresh guild keys')
		if cooldown > 0 then
			local minutes = math.floor(cooldown / 60)
			local seconds = cooldown % 60
			GameTooltip:AddLine(format('Available in %d:%02d', minutes, seconds), 1, 1, 1)
		else
			GameTooltip:AddLine('Ready', 0.4, 1, 0.4)
		end
		GameTooltip:Show()
	end)
	guildRefreshButton:SetScript('OnLeave', GameTooltip_Hide)
	guildRefreshButton:SetScript('OnUpdate', function(self, elapsed)
		self._cooldownTick = (self._cooldownTick or 0) + elapsed
		if self._cooldownTick >= 1 then
			self._cooldownTick = 0
			SetGuildStatus()
		end
	end)

	local header = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	header:SetPoint('TOPLEFT', 18, -38)
	header:SetText('Player iLvL')
	frame.HeaderPlayer = header
	local headerKey = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	headerKey:SetPoint('TOPLEFT', 170, -38)
	headerKey:SetText('Keystone')
	frame.HeaderKey = headerKey
	local headerBest = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	headerBest:SetPoint('TOPRIGHT', -4, -38)
	headerBest:SetWidth(70)
	headerBest:SetJustifyH('RIGHT')
	headerBest:SetText('Best')
	frame.HeaderBest = headerBest

	guildScroll = CreateFrame('ScrollFrame', nil, frame, 'UIPanelScrollFrameTemplate')
	guildScroll:SetPoint('TOPLEFT', 14, -58)
	guildScroll:SetPoint('BOTTOMRIGHT', -30, 14)
	guildScrollChild = CreateFrame('Frame', nil, guildScroll)
	guildScrollChild:SetWidth(GUILD_WINDOW_WIDTH - 48)
	guildScrollChild:SetHeight(1)
	guildScroll:SetScrollChild(guildScrollChild)


	guildWindow = frame
	UpdateGuildRows()
end

function Mod:SetGuildWindowOpen(open)
	guildWindowOpen = open and true or false
	if AngryKeystones_Config then
		AngryKeystones_Config.guildKeysOpen = guildWindowOpen
	end
	if Mod.GuildButton then
		Mod.GuildButton:SetText(guildWindowOpen and 'Hide Guild' or 'Guild Keys')
	end
	if guildWindowOpen then
		if not ChallengesFrame or not ChallengesFrame:IsShown() then
			if not ChallengesFrame and LoadAddOn then pcall(LoadAddOn, 'Blizzard_ChallengesUI') end
			if PVEFrame_ShowFrame then pcall(PVEFrame_ShowFrame, 'ChallengesFrame') end
		end
		CreateGuildWindow()
		if ChallengesFrame and ChallengesFrame.GetHeight then guildWindow:SetHeight(ChallengesFrame:GetHeight()) end
		UpdateGuildRows()
		if ChallengesFrame and ChallengesFrame:IsShown() then
			guildWindow:Show()
		else
			HideGuildWindow()
		end
	else
		HideGuildWindow()
	end
end

function Mod:ShowGuildKeys()
	self:SetGuildWindowOpen(true)
end

function Mod:HideGuildKeys(clearPreference)
	if clearPreference then
		self:SetGuildWindowOpen(false)
	else
		HideGuildWindow()
	end
end

function Mod:ToggleGuildKeys()
	self:SetGuildWindowOpen(not guildWindowOpen)
end

function Mod:RequestGuildKeys(force)
	if not IsInGuild() then
		if Mod.GuildButton then Mod.GuildButton:Hide() end
		return
	end
	local cooldown = GetGuildRequestCooldown()
	if cooldown > 0 and not force then
		self:ShowGuildKeys()
		return
	elseif cooldown > 0 then
		SetGuildStatus()
		return
	end

	lastGuildRequest = time()
	if AngryKeystones_Config then AngryKeystones_Config.guildKeysLastRequest = lastGuildRequest end
	guildCache = {}
	guildCacheTime = time()
	local requestID = tostring(time()) .. tostring(math.random(100, 999))
	SendAddonMessage(PARTY_PREFIX, REQUEST .. ':GUILD:' .. requestID, 'GUILD')
	SendOwnKeystone(true, requestID, 'GUILD')
	self:ShowGuildKeys()
	SetGuildStatus()

	-- Repaint the status after a short collection window without creating a
	-- repeating OnUpdate or any permanent timer.
	if C_Timer and C_Timer.After then
		C_Timer.After(3, function()
			if guildWindow then UpdateGuildRows() end
		end)
	end
end

local function IsKeyRequest(message)
	if not message then return false end
	message = message:lower()
	return message:match('^%s*[!?]keys?%s*$') ~= nil or message:match('^%s*keys?[!?]%s*$') ~= nil
end

local function GetChatSenderKey(sender)
	return sender and (sender:match('^([^%-]+)') or sender) or ''
end

local function HandleChatKeyRequest(message, channel, sender)
	if not IsKeyRequest(message) or not sender or sender == GetPlayerName() then return end
	local senderKey = GetChatSenderKey(sender)
	local now = time()
	local lastRequest = chatRequestCooldowns[senderKey]
	if lastRequest and now - lastRequest < CHAT_REQUEST_COOLDOWN then return end
	chatRequestCooldowns[senderKey] = now

	if not ownKeystone then RefreshOwnKeystone() end
	if ownKeystone and ownKeystone.link then
		SendChatMessage(ownKeystone.link, channel)
	else
		SendChatMessage('No keystone.', channel)
	end
end

function Mod:CHAT_MSG_PARTY(message, sender)
	if IsKeyRequest(message) then
		local requester = GetChatSenderKey(sender)
		if requester ~= GetPlayerName() then
			-- Everyone answers the request through addon messages as well as the
			-- visible party key link, so the existing party panel stays current.
			SendOwnKeystone(true, requester, 'PARTY')
		end
	end
	HandleChatKeyRequest(message, 'PARTY', sender)
	if IsKeyRequest(message) and sender == GetPlayerName() then
		local now = time()
		if now - lastOwnPartyChatRequest >= CHAT_REQUEST_COOLDOWN then
			lastOwnPartyChatRequest = now
			RequestPartyKeys()
		end
	end
end

function Mod:CHAT_MSG_GUILD(message, sender)
	-- Chat key requests are intentionally disabled for guild chat now that the
	-- Guild Keys window provides a dedicated, non-spammy collection UI.
end

function Mod:CHAT_MSG_ADDON(prefix, message, channel, sender)
	if prefix ~= PARTY_PREFIX then return end
	local parts = { strsplit(':', message) }
	local kind = parts[1]

	if kind == REQUEST then
		local scope, requestID = parts[2], parts[3]
		if scope == 'PARTY' and channel == 'PARTY' and IsRegularParty() then
			SendOwnKeystone(true, requestID or 'PARTY', 'PARTY')
		elseif scope == 'GUILD' and channel == 'GUILD' and requestID and sender ~= GetPlayerName() then
			if C_Timer and C_Timer.After then
				C_Timer.After(math.random(1, 12) / 10, function()
					SendOwnKeystone(true, requestID, 'GUILD')
				end)
			else
				SendOwnKeystone(true, requestID, 'GUILD')
			end
		end
		return
	end

	if kind ~= RESPONSE then return end
	local requestID = parts[2]
	local mapID = tonumber(parts[3])
	local level = tonumber(parts[4])
	local best = tonumber(parts[5])
	local class = parts[6]
	local name = parts[7]
	local mapName = parts[8]
	local ilvl = tonumber(parts[9]) or 0
	local specID = tonumber(parts[10]) or 0
	local specName = parts[11] or ''
	local specIcon = parts[12] or ''
	if not mapID or not level then return end
	local entry = { mapID = mapID, level = level, weeklyBest = best or 0, class = class, mapName = mapName, ilvl = ilvl, specID = specID, specName = specName, specIcon = specIcon, hasAddon = true }
	if channel == 'PARTY' and not IsRegularParty() then
		return
	end
	if channel == 'PARTY' then
		local old = partyKeys[sender] or partyKeys[sender:match('^([^%-]+)')]
		if old and GetKeySignature(old) ~= GetKeySignature(entry) then
			entry.changedUntil = GetTime() + 7
		end
	end
	local shortSender = sender:match('^([^%-]+)') or sender

	if channel == 'PARTY' then
		partyKeys[sender] = entry
		partyKeys[shortSender] = entry
		UpdatePartyRows()
	elseif channel == 'GUILD' and requestID then
		local responseName = name and name ~= '' and name or sender
		guildCache[responseName] = entry
		guildCacheTime = time()
		UpdateGuildRows()
	end
end

function Mod:CHALLENGE_MODE_COMPLETED()
	if C_ChallengeMode and C_ChallengeMode.GetCompletionInfo then
		local _, level = C_ChallengeMode.GetCompletionInfo()
		if level then SaveWeeklyBest(level) end
	end
	RefreshOwnKeystone()
	UpdatePartyRows()
end

function Mod:GROUP_ROSTER_UPDATE()
	if not IsRegularParty() then
		partyKeys = {}
		partyRequestStarted = 0
	end
	UpdatePartyRows()
	if Mod.GuildButton then Mod.GuildButton:SetShown(IsInGuild()) end
	RequestPartyKeys()
end

function Mod:BAG_UPDATE()
	requestKeystoneCheck = true
	RefreshOwnKeystone()
	if Mod.PartyFrame then
		UpdateAffixes()
		SendOwnKeystone(false)
	end
end

function Mod:CheckInventoryKeystone()
	local foundWeek
	local best = FindBestKeystone()
	if best then
		for container = BACKPACK_CONTAINER, NUM_BAG_SLOTS do
			local slots = GetContainerNumSlots(container)
			for slot = 1, slots do
				local _, _, _, _, _, _, slotLink = GetContainerItemInfo(container, slot)
				local itemString = slotLink and slotLink:match('|Hkeystone:([0-9:]+)|h')
				if itemString then
					local info = { strsplit(':', itemString) }
					local mapLevel = tonumber(info[2])
					if mapLevel and mapLevel >= 7 then
						local affix1, affix2 = tonumber(info[3]), tonumber(info[4])
						for index, affixes in ipairs(affixSchedule) do
							if affix1 == affixes[1] and affix2 == affixes[2] then foundWeek = index end
						end
					end
				end
			end
		end
	end
	currentWeek = foundWeek or GetRotationWeek()
	ownKeystone = best
	if ownKeystone and C_ChallengeMode and C_ChallengeMode.GetMapInfo then
		ownKeystone.mapName = C_ChallengeMode.GetMapInfo(ownKeystone.mapID)
	end
	previousKeySignature = GetKeySignature(best)
	requestKeystoneCheck = false
end

function Mod:Blizzard_ChallengesUI()
	ChallengesFrame.GuildBest:ClearAllPoints()
	ChallengesFrame.GuildBest:SetPoint('TOPLEFT', ChallengesFrame.WeeklyBest.Child.Star, 'BOTTOMRIGHT', 9, 30)

	local container = CreateFrame('Frame', nil, ChallengesFrame)
	container:SetSize(535, 165)
	container:SetPoint('TOP', ChallengesFrame.WeeklyBest.Child.Star, 'BOTTOM', 0, 54)
	container:SetPoint('LEFT', ChallengesFrame, 'LEFT', 40, 0)
	Mod.Container = container

	local frame = makePanel(container, 206, Addon.Locale.scheduleTitle)
	frame:SetHeight(140)
	frame:SetPoint('LEFT', container, 'LEFT', 0, 0)
	Mod.Frame = frame

	local entries = {}
	for i = 1, rowCount do
		local entry = CreateFrame('Frame', nil, frame)
		entry:SetSize(176, 18)
		local text = entry:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
		text:SetWidth(120)
		text:SetJustifyH('LEFT')
		text:SetWordWrap(false)
		text:SetText(Addon.Locale['scheduleWeek' .. i])
		text:SetPoint('LEFT')
		entry.Text = text
		local affixes = {}
		local prevAffix
		for j = 3, 1, -1 do
			local affix = makeAffix(entry)
			if prevAffix then affix:SetPoint('RIGHT', prevAffix, 'LEFT', -4, 0) else affix:SetPoint('RIGHT') end
			prevAffix = affix
			affixes[j] = affix
		end
		entry.Affixes = affixes
		if i == 1 then entry:SetPoint('TOP', frame.Line, 'BOTTOM') else entry:SetPoint('TOP', entries[i - 1], 'BOTTOM') end
		entries[i] = entry
	end
	frame.Entries = entries

	local label = frame:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
	label:SetPoint('TOPLEFT', frame.Line, 'BOTTOMLEFT', 10, 0)
	label:SetPoint('TOPRIGHT', frame.Line, 'BOTTOMRIGHT', -10, 0)
	label:SetJustifyH('CENTER')
	label:SetJustifyV('MIDDLE')
	label:SetHeight(84)
	label:SetWordWrap(true)
	label:SetText('')
	frame.Label = label

	local party = makePanel(container, 320, 'Party Keystones')
	party:SetHeight(140)
	party:SetPoint('LEFT', frame, 'RIGHT', 4, 24)
	Mod.PartyFrame = party
	local partyHeader = party:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	partyHeader:SetPoint('TOPLEFT', party.Line, 'BOTTOMLEFT', 10, 1)
	partyHeader:SetText('Player iLvL')
	party.HeaderPlayer = partyHeader
	local partyKeyHeader = party:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	partyKeyHeader:SetPoint('TOPLEFT', party.Line, 'BOTTOMLEFT', 10 + PARTY_MIN_NAME_WIDTH + 8, 1)
	partyKeyHeader:SetText('Keystone')
	party.HeaderKey = partyKeyHeader
	local partyBestHeader = party:CreateFontString(nil, 'ARTWORK', 'GameFontNormalSmall')
	partyBestHeader:SetPoint('TOPRIGHT', party.Line, 'BOTTOMRIGHT', -8, 1)
	partyBestHeader:SetText('Best')
	party.HeaderBest = partyBestHeader

	local partyEntries = {}
	for i = 1, 5 do
		local entry = CreateFrame('Frame', nil, party)
		entry:SetSize(290, 18)
		entry:SetPoint('TOPLEFT', party, 'TOPLEFT', 10, -48 - ((i - 1) * 18))
		local highlight = entry:CreateTexture(nil, 'BACKGROUND')
		highlight:SetAllPoints()
		highlight:SetAtlas('ChallengeMode-guild-background')
		highlight:Hide()
		entry.Highlight = highlight
		local text = entry:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
		text:SetWidth(100)
		text:SetJustifyH('LEFT')
		text:SetWordWrap(false)
		text:SetPoint('LEFT')
		entry.Text = text
		local key = entry:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
		key:SetWidth(PARTY_MIN_KEY_WIDTH)
		key:SetJustifyH('LEFT')
		key:SetWordWrap(false)
		key:SetPoint('LEFT', entry, 'LEFT', 10 + PARTY_MIN_NAME_WIDTH + 8, 0)
		entry.Key = key
		local best = entry:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
		best:SetWidth(42)
		best:SetJustifyH('LEFT')
		best:SetPoint('LEFT', entry, 'LEFT', 10 + PARTY_MIN_NAME_WIDTH + 8 + PARTY_MIN_KEY_WIDTH + 8, 0)
		entry.Best = best
		partyEntries[i] = entry
	end
	party.Entries = partyEntries
	local empty = party:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
	empty:SetPoint('TOPLEFT', party.Line, 'BOTTOMLEFT', 10, -55)
	empty:SetPoint('TOPRIGHT', party.Line, 'BOTTOMRIGHT', -10, -55)
	empty:SetJustifyH('CENTER')
	empty:SetText('No party members')
	party.Empty = empty

	local guildButton = CreateFrame('Button', nil, container, 'UIPanelButtonTemplate')
	guildButton:SetSize(92, 22)
	guildButton:SetPoint('TOPRIGHT', party, 'TOPRIGHT', -6, -3)
	guildButton:SetText('Guild Keys')
	guildButton:SetScript('OnClick', function() Mod:ToggleGuildKeys() end)
	Mod.GuildButton = guildButton
	guildButton:SetText(guildWindowOpen and 'Hide Guild' or 'Guild Keys')

	hooksecurefunc('ChallengesFrame_Update', UpdateAffixes)
	ChallengesFrame:HookScript('OnHide', function() HideGuildWindow() end)
	ChallengesFrame:HookScript('OnShow', function()
		if guildWindowOpen then
			CreateGuildWindow()
			guildWindow:Show()
			UpdateGuildRows()
		end
	end)
	UpdateAffixes()
	RequestPartyKeys()
	guildWindowOpen = AngryKeystones_Config and AngryKeystones_Config.guildKeysOpen == true or false
	guildButton:SetText(guildWindowOpen and 'Hide Guild' or 'Guild Keys')
	if guildWindowOpen and ChallengesFrame:IsShown() then
		CreateGuildWindow()
		guildWindow:Show()
	end
end

function Mod:SlashCommand(msg)
	msg = (msg or ''):lower():gsub('^%s+', ''):gsub('%s+$', '')
	if msg == 'guild' or msg == 'guildkeys' or msg == 'gkeys' then
		self:RequestGuildKeys(false)
		return true
	end
	return false
end

local function OpenAddonOptions()
	if SlashCmdList and SlashCmdList.AngryKeystones then
		SlashCmdList.AngryKeystones('')
	end
end

local function SaveMinimapButtonPosition(button)
	if not button or not Minimap or not AngryKeystones_Config then return end
	local cx, cy = Minimap:GetCenter()
	local bx, by = button:GetCenter()
	if not cx or not cy or not bx or not by then return end
	local angle = math.deg(math.atan2(by - cy, bx - cx))
	AngryKeystones_Config.minimapButtonAngle = angle
end

local function RestoreMinimapButtonPosition(button)
	if not button or not Minimap then return end
	local angle = tonumber(AngryKeystones_Config and AngryKeystones_Config.minimapButtonAngle) or 45
	local rad = math.rad(angle)
	button:ClearAllPoints()
	button:SetPoint('CENTER', Minimap, 'CENTER', math.cos(rad) * MINIMAP_BUTTON_RADIUS, math.sin(rad) * MINIMAP_BUTTON_RADIUS)
end

local function ToggleChallengesFrame()
	if not ChallengesFrame and LoadAddOn then pcall(LoadAddOn, 'Blizzard_ChallengesUI') end
	-- ChallengesFrame is only the content panel. Hiding it directly leaves the
	-- PVEFrame shell visible. Use Blizzard's own PVE toggle so the whole window
	-- opens/closes exactly like the normal Mythic Dungeons button.
	if PVEFrame_ToggleFrame then
		pcall(PVEFrame_ToggleFrame, 'ChallengesFrame')
		return
	end
	if ChallengesFrame and ChallengesFrame:IsShown() then
		if PVEFrame then PVEFrame:Hide() else ChallengesFrame:Hide() end
	elseif PVEFrame_ShowFrame then
		pcall(PVEFrame_ShowFrame, 'ChallengesFrame')
	elseif ChallengesFrame then
		ChallengesFrame:Show()
	end
end

local function CreateMinimapButton()
	if minimapButton or not Minimap then return end
	local button = CreateFrame('Button', ADDON .. 'MinimapButton', Minimap)
	button:SetSize(32, 32)
	button:SetFrameStrata('MEDIUM')
	button:SetFrameLevel(8)
	button:RegisterForClicks('LeftButtonUp', 'RightButtonUp')
	button:RegisterForDrag('LeftButton')
	button:SetMovable(true)
	button:SetClampedToScreen(true)
	button:SetHighlightTexture('Interface\\Minimap\\UI-Minimap-ZoomButton-Highlight')

	local iconBackdrop = button:CreateTexture(nil, 'BACKGROUND')
	iconBackdrop:SetTexture('Interface\\Buttons\\WHITE8X8')
	iconBackdrop:SetSize(25, 19)
	iconBackdrop:SetPoint('CENTER', button, 'CENTER', 0, -1)
	iconBackdrop:SetVertexColor(0, 0, 0, 0.55)
	button.IconBackdrop = iconBackdrop

	local icon = button:CreateFontString(nil, 'ARTWORK', 'GameFontNormal')
	icon:SetPoint('CENTER', button, 'CENTER', 0, -1)
	icon:SetWidth(28)
	icon:SetHeight(20)
	icon:SetJustifyH('CENTER')
	icon:SetJustifyV('MIDDLE')
	icon:SetText('M+')
	icon:SetTextColor(1.0, 0.82, 0.0)
	icon:SetShadowOffset(2, -2)
	icon:SetShadowColor(0, 0, 0, 1)
	button.Icon = icon
	button.IconPlus = nil


	local border = button:CreateTexture(nil, 'OVERLAY')
	border:SetTexture('Interface\\Minimap\\MiniMap-TrackingBorder')
	border:SetSize(54, 54)
	border:SetPoint('TOPLEFT', button, 'TOPLEFT', 0, 0)
	button.Border = border

	local dragging = false
	button:SetScript('OnDragStart', function(self)
		dragging = true
		self:StartMoving()
	end)
	button:SetScript('OnDragStop', function(self)
		self:StopMovingOrSizing()
		dragging = false
		SaveMinimapButtonPosition(self)
		RestoreMinimapButtonPosition(self)
	end)
	button:SetScript('OnClick', function(self, mouseButton)
		if dragging then return end
		if mouseButton == 'RightButton' then
			OpenAddonOptions()
			return
		end
		ToggleChallengesFrame()
	end)
	button:SetScript('OnEnter', function(self)
		GameTooltip:SetOwner(self, 'ANCHOR_LEFT')
		GameTooltip:SetText('Angry Keystones')
		GameTooltip:AddLine('Left-click: open/close Mythic Dungeons', 1, 1, 1)
		GameTooltip:AddLine('Right-click: options', 1, 1, 1)
		GameTooltip:AddLine('Drag: move minimap button', 1, 1, 1)
		GameTooltip:Show()
	end)
	button:SetScript('OnLeave', GameTooltip_Hide)
	minimapButton = button
	RestoreMinimapButtonPosition(button)
	button:SetShown(not (Addon.Config and Addon.Config.Get and Addon.Config:Get('showMinimapButton') == false))
end

function Mod:SetMinimapButtonShown(show)
	if not minimapButton then CreateMinimapButton() end
	if minimapButton then minimapButton:SetShown(show and true or false) end
end

function Mod:Startup()
	self:RegisterAddOnLoaded('Blizzard_ChallengesUI')
	self:RegisterEvent('BAG_UPDATE')
	self:RegisterEvent('GROUP_ROSTER_UPDATE')
	self:RegisterEvent('CHAT_MSG_ADDON')
	self:RegisterEvent('CHAT_MSG_PARTY')
	self:RegisterEvent('CHAT_MSG_GUILD')
	self:RegisterEvent('CHALLENGE_MODE_COMPLETED')
	RegisterAddonMessagePrefix(PARTY_PREFIX)
	requestKeystoneCheck = true
	LoadWeeklyBest()
	lastGuildRequest = tonumber(AngryKeystones_Config and AngryKeystones_Config.guildKeysLastRequest) or 0
	guildWindowOpen = AngryKeystones_Config and AngryKeystones_Config.guildKeysOpen == true or false
	previousKeySignature = GetKeySignature(FindBestKeystone())
	CreateMinimapButton()
	if Addon.Config and Addon.Config.RegisterCallback then
		Addon.Config:RegisterCallback('showMinimapButton', function(_, value) Mod:SetMinimapButtonShown(value) end)
	end
end

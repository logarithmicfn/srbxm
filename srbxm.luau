--!native

local encodingService = game:GetService("EncodingService")

local rad = math.rad

local band = bit32.band
local bor = bit32.bor
local lshift = bit32.lshift
local rshift = bit32.rshift
local rrotate = bit32.rrotate

local bufferCreate = buffer.create
local fromstring = buffer.fromstring
local len = buffer.len
local read = buffer.readstring
local readu8 = buffer.readu8
local readu32 = buffer.readu32
local readu16 = buffer.readu16
local readf32 = buffer.readf32
local readf64 = buffer.readf64

local tableCreate = table.create
local insert = table.insert
local copy = buffer.copy
local writeu8 = buffer.writeu8
local writeu32 = buffer.writeu32
local rrotate = bit32.rrotate

local udim = UDim.new
local udim2 = UDim2.new
local ray = Ray.new
local vector3 = Vector3.new
local faces = Faces.new
local axes = Axes.new
local brickColor = BrickColor.new
local color3 = Color3.new
local color3FromRGB = Color3.fromRGB
local vector2 = Vector2.new
local cframe = CFrame.new
local cframeAngles = CFrame.Angles
local vector3int16 = Vector3int16.new
local numberSequence = NumberSequence.new
local numberSequenceKeypoint = NumberSequenceKeypoint.new
local colorSequence = ColorSequence.new
local colorSequenceKeypoint = ColorSequenceKeypoint.new
local numberRange = NumberRange.new
local rect = Rect.new
local physicalProperties = PhysicalProperties.new
local font = Font.new
local contentNone = Content.none
local contentFromUri = Content.fromUri
local contentFromObject = Content.fromObject

local fontWeight = Enum.FontWeight
local fontStyle = Enum.FontStyle
local normalId = Enum.NormalId
local axis = Enum.Axis

local top = normalId.Top
local back = normalId.Back
local left = normalId.Left
local front = normalId.Front
local right = normalId.Right
local bottom = normalId.Bottom

local axisX = axis.X
local axisY = axis.Y
local axisZ = axis.Z

local zstd = Enum.CompressionAlgorithm.Zstd

local fontWeightFromValue = fontWeight.FromValue
local fontStyleFromValue = fontStyle.FromValue
local decompressBuffer = encodingService.DecompressBuffer

local orientations = {
	[0x02] = cframe(),
	[0x03] = cframeAngles(rad(90),0,0),
	[0x05] = cframeAngles(0,rad(180),rad(180)),
	[0x06] = cframeAngles(rad(-90), 0,0),
	[0x07] = cframeAngles(0,rad(180),rad(90)),
	[0x09] = cframeAngles(0,rad(90),rad(90)),
	[0x0A] = cframeAngles(0,0,rad(90)),
	[0x0C] = cframeAngles(0,rad(-90),rad(90)),
	[0x0D] = cframeAngles(rad(-90),rad(-90), 0),
	[0x0E] = cframeAngles(0,rad(-90),0),
	[0x10] = cframeAngles(rad(90),rad(-90), 0),
	[0x11] = cframeAngles(0,rad(90),rad(180)),
	[0x14] = cframeAngles(0,rad(180),0),
	[0x15] = cframeAngles(rad(-90),rad(-180), 0),
	[0x17] = cframeAngles(0,0,rad(180)),
	[0x18] = cframeAngles(rad(90),rad(180), 0),
	[0x19] = cframeAngles(0,0,rad(-90)),
	[0x1B] = cframeAngles(0,rad(-90), rad(-90)),
	[0x1C] = cframeAngles(0,rad(-180), rad(-90)),
	[0x1E] = cframeAngles(0,rad(90),rad(-90)),
	[0x1F] = cframeAngles(rad(90),rad(90),0),
	[0x20] = cframeAngles(0,rad(90),0),
	[0x22] = cframeAngles(rad(-90),rad(90),0),
	[0x23] = cframeAngles(0,rad(-90),rad(180))
}

local function lz4(input,uncompressedLength)
	local output = bufferCreate(uncompressedLength)

	local inputPosition = 0
	local outputPosition = 0

	while outputPosition < uncompressedLength do
		local token = readu8(input,inputPosition) inputPosition += 1
		local literalLength = token // 0x10
		local matchLength = token % 0x10

		if literalLength == 0x0F then
			repeat
				local extra = readu8(input,inputPosition)
				literalLength += extra
				inputPosition += 1
			until extra ~= 0xFF
		end

		if literalLength > 0 then
			copy(output,outputPosition,input,inputPosition,literalLength)
			inputPosition += literalLength
			outputPosition += literalLength

			if outputPosition >= uncompressedLength then 
				break 
			end
		end

		local readback = readu16(input,inputPosition) inputPosition += 2
		local copyStart = outputPosition - readback

		if matchLength == 0x0F then
			repeat
				local extra = readu8(input,inputPosition)
				matchLength += extra
				inputPosition += 1
			until extra ~= 0xFF
		end
		matchLength += 4

		while matchLength > 0 do
			local available = outputPosition - copyStart

			local toCopy = matchLength
			if toCopy > available then toCopy = available end

			copy(output,outputPosition,output,copyStart,toCopy)
			outputPosition += toCopy
			matchLength -= toCopy
		end
	end

	return output
end

local function readString(buffer,position)
	local length = readu32(buffer,position) position += 4
	local string = read(buffer,position,length) position += length
	return string,position
end

local function bswap32(x)
	return bor(
		lshift(band(x,0xFF),24),
		lshift(band(x,0xFF00),8),
		rshift(band(x,0xFF0000),8),
		rshift(x,24)
	)
end

-- Because Luau's buffer library doesn't include 64-bit integers, a custom function is required.
-- The same logic is used for Roblox 64-bit integers.

local function readi64(buffer,position)
	local high = readu32(buffer,position) position += 4
	local low = readu32(buffer,position) position += 4
	return high * 2 ^ 32 + low
end

-- Roblox floats/integers use big-endianness.
-- Roblox floats do NOT follow the IEEE-754 standard, they instead follow a proprietary format.
-- To make compression easier, Roblox integers use a transformation and every array is interleaved.

local function transform(x)
	return x % 2 == 0 and x / 2 or -(x + 1) / 2
end

local function readRBXi32(buffer,position)
	local value = bswap32(readu32(buffer,position)) position += 4
	return transform(value),position
end

local function readRBXi64(buffer,position)
	local high = bswap32(readu32(buffer,position)) position += 4
	local low = bswap32(readu32(buffer,position)) position += 4
	return transform(high * 2 ^ 32 + low),position
end

local scratch = buffer.create(4)
local function readRBXf32(buffer,position)
	writeu32(scratch,0,bswap32(rrotate(readu32(buffer,position),1))) position += 4
	return readf32(scratch,0),position
end

local function interleave(buffer,position,count,length)
	local total = count * length

	local output = bufferCreate(total)
	for source = 0,total - 1 do
		local value = readu8(buffer,position + source)
		local destination = (source % count) * length + (source // count)
		writeu8(output,destination,value)
	end

	return output,position + total
end

local function readRBXi32Array(buffer,position,count)
	local array = tableCreate(count)
	local interleaved
	interleaved,position = interleave(buffer,position,count,4)	

	local interleavedPosition = 0
	for i = 1,count do
		array[i],interleavedPosition = readRBXi32(interleaved,interleavedPosition)
	end

	return array,position
end

local function readRBXi64Array(buffer,position,count)
	local array = tableCreate(count)
	local interleaved
	interleaved,position = interleave(buffer,position,count,8)	

	local interleavedPosition = 0
	for i = 1,count do
		array[i],interleavedPosition = readRBXi64(interleaved,interleavedPosition)
	end

	return array,position
end

local function readRBXf32Array(buffer,position,count)
	local array = tableCreate(count)
	local interleaved
	interleaved,position = interleave(buffer,position,count,4)	

	local interleavedPosition = 0
	for i = 1,count do
		array[i],interleavedPosition = readRBXf32(interleaved,interleavedPosition)
	end

	return array,position
end

local function readReferentArray(buffer,position,count)
	local array = tableCreate(count)
	local references
	references,position = readRBXi32Array(buffer,position,count)

	local accumulator = 0
	for i = 1,count do
		accumulator += references[i]
		array[i] = accumulator
	end

	return array,position
end

local function readu32BEArray(buffer,position,count)
	local array = tableCreate(count)
	local interleaved
	interleaved,position = interleave(buffer,position,count,4)	

	local interleavedPosition = 0
	for i = 1,count do
		array[i] = bswap32(readu32(interleaved,interleavedPosition)) interleavedPosition += 4
	end

	return array,position
end

local function srbxm(rbxm)
	assert(read(rbxm,0,8) == "<roblox!","invalid RBXM header")
	assert(read(rbxm,8,6) == "\x89\xff\x0d\x0a\x1a\x0a","invalid RBXM signature")
	assert(read(rbxm,14,2) == "\0\0","unsupported RBXM version")
	local size = {
		classes = readu32(rbxm,16),
		instances = readu32(rbxm,20)
	}
	assert(read(rbxm,24,8) == "\0\0\0\0\0\0\0\0","bad RBXM header")
	
	local classes = {}
	local instances = {}
	
	local metadata = {}
	local strings = {}
	local instances = {}
	
	local position = 32
	while true do
		local chunkName = read(rbxm,position,4) position += 4
		local compressedLength = readu32(rbxm,position) position += 4
		local uncompressedLength = readu32(rbxm,position) position += 4
		assert(read(rbxm,position,4) == "\0\0\0\0","bad chunk header") position += 4
		
		local compressed = compressedLength > 0
		local length = compressed and compressedLength or uncompressedLength
		local chunk = bufferCreate(length)
		copy(chunk,0,rbxm,position,length) position += length
		
		if compressed then
			if read(chunk,0,4) == "\x28\xB5\x2F\xFD" then -- If there is a ZSTD header, use EncodingService to decompress the chunk.
				chunk = decompressBuffer(encodingService,chunk,zstd)
			else
				chunk = lz4(chunk,uncompressedLength)
			end 
		end
		
		local position = 0
		if chunkName == "META" then
			local entriesCount = readu32(chunk,position) position += 4
			for i = 1,entriesCount do
				local key,value
				key,position = readString(chunk,position)
				value,position = readString(chunk,position)
				metadata[key] = value
			end
		elseif chunkName == "SSTR" then
			assert(readu32(chunk,position) == 0,"unsupported SSTR version") position += 4
			local sharedStringCount = readu32(chunk,position) position += 4
			for i = 1,sharedStringCount do
				position += 16 -- This is an MD5 hash.
				local sharedString
				sharedString,position = readString(chunk,position)
				table.insert(strings,sharedString)
			end
		elseif chunkName == "INST" then
			local classId = readu32(chunk,position) position += 4
			local className
			className,position = readString(chunk,position)

			local service = readu8(chunk,position) == 1 position += 1
			
			local instanceCount = readu32(chunk,position) position += 4
			local referents
			referents,position = readReferentArray(chunk,position,instanceCount)
			classes[classId] = referents

			for i,referent in referents do
				instances[referent] = {
					class = className,
					properties = {},
					children = {},
					service = service and service or nil
				}
			end
		elseif chunkName == "PROP" then
			local classId = readu32(chunk,position) position += 4
			local referents = classes[classId]
			local instanceCount = #referents
	
			local propertyName
			propertyName,position = readString(chunk,position)

			local typeId = readu8(chunk,position) position += 1
			local optionalCFrame = typeId == 0x1E
			if optionalCFrame then
				typeId = readu8(chunk,position) position += 1
			end

			local values = {}
			
			if typeId == 0x01 then -- String
				for referentIndex = 1,instanceCount do
					values[referentIndex],position = readString(chunk,position)
				end
			elseif typeId == 0x02 then -- Boolean
				for referentIndex = 1,instanceCount do
					values[referentIndex] = readu8(chunk,position) == 1 position += 1
				end
			elseif typeId == 0x03 then -- Roblox i32
				values,position = readRBXi32Array(chunk,position,instanceCount)
			elseif typeId == 0x04 then -- Roblox f32
				values,position = readRBXf32Array(chunk,position,instanceCount)
			elseif typeId == 0x05 then -- f64
				for referentIndex = 1,instanceCount do
					values[referentIndex] = readf64(chunk,position,instanceCount) position += 8
				end
			elseif typeId == 0x06 then -- UDim
				local scale,offset
				scale,position = readRBXf32Array(chunk,position,instanceCount)
				offset,position = readRBXi32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = udim(scale[referentIndex],offset[referentIndex])
				end
			elseif typeId == 0x07 then -- UDim2
				local scaleX,scaleY,offsetX,offsetY 
				scaleX,position = readRBXf32Array(chunk,position,instanceCount)
				scaleY,position = readRBXf32Array(chunk,position,instanceCount)
				offsetX,position = readRBXi32Array(chunk,position,instanceCount)
				offsetY,position = readRBXi32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = udim2(scaleX[referentIndex],offsetX[referentIndex],scaleY[referentIndex],offsetY[referentIndex])
				end
			elseif typeId == 0x08 then -- Ray
				for referentIndex = 1,instanceCount do
					local originX = readf32(chunk,position) position += 4
					local originY = readf32(chunk,position) position += 4
					local originZ = readf32(chunk,position) position += 4
					local directionX = readf32(chunk,position) position += 4
					local directionY = readf32(chunk,position) position += 4
					local directionZ = readf32(chunk,position) position += 4
					values[referentIndex] = ray(vector3(originX,originY,originZ),vector3(directionX,directionY,directionZ))
				end
			elseif typeId == 0x09 then -- Faces
				for referentIndex = 1,instanceCount do
					local flag = readu8(chunk,position) position += 1
					values[referentIndex] = faces(
						band(flag,1) ~= 0 and right,
						band(flag,2) ~= 0 and top,
						band(flag,4) ~= 0 and back,
						band(flag,8) ~= 0 and left,
						band(flag,16) ~= 0 and bottom,
						band(flag,32) ~= 0 and front
					)
				end
			elseif typeId == 0x0A then -- Axes
				for referentIndex = 1,instanceCount do
					local flag = readu8(chunk,position) position += 1
					values[referentIndex] = {
						band(flag,1) ~= 0 and axisX,
						band(flag,2) ~= 0 and axisY,
						band(flag,4) ~= 0 and axisZ
					}
				end
			elseif typeId == 0x0B then -- BrickColor
				local numbers = readu32BEArray(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = brickColor(numbers[referentIndex])
				end
			elseif typeId == 0x0C then -- Color3
				local r,g,b
				r,position = readRBXf32Array(chunk,position,instanceCount)
				g,position = readRBXf32Array(chunk,position,instanceCount)
				b,position = readRBXf32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = color3(r[referentIndex],g[referentIndex],b[referentIndex])
				end
			elseif typeId == 0x0D then -- Vector2
				local x,y
				x,position = readRBXf32Array(chunk,position,instanceCount)
				y,position = readRBXf32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = vector2(x[referentIndex],y[referentIndex])
				end
			elseif typeId == 0X0E then -- Vector3
				local x,y,z
				x,position = readRBXf32Array(chunk,position,instanceCount)
				y,position = readRBXf32Array(chunk,position,instanceCount)
				z,position = readRBXf32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = vector3(x[referentIndex],y[referentIndex],z[referentIndex])
				end
			elseif typeId == 0x10 then -- CFrame
				local r00 = tableCreate(instanceCount)
				local r01 = tableCreate(instanceCount)
				local r02 = tableCreate(instanceCount)
				local r10 = tableCreate(instanceCount)
				local r11 = tableCreate(instanceCount)
				local r12 = tableCreate(instanceCount)
				local r20 = tableCreate(instanceCount)
				local r21 = tableCreate(instanceCount)
				local r22 = tableCreate(instanceCount)
				for referentIndex = 1,instanceCount do
					local orientationId = readu8(chunk,position) position += 1
					if orientationId == 0 then
						local a00 = readf32(chunk,position) position += 4
						local a01 = readf32(chunk,position) position += 4
						local a02 = readf32(chunk,position) position += 4
						local a10 = readf32(chunk,position) position += 4
						local a11 = readf32(chunk,position) position += 4
						local a12 = readf32(chunk,position) position += 4
						local a20 = readf32(chunk,position) position += 4
						local a21 = readf32(chunk,position) position += 4
						local a22 = readf32(chunk,position) position += 4
						r00[referentIndex],r01[referentIndex],r02[referentIndex] = a00,a01,a02
						r10[referentIndex],r11[referentIndex],r12[referentIndex] = a10,a11,a12
						r20[referentIndex],r21[referentIndex],r22[referentIndex] = a20,a21,a22
					else
						values[referentIndex] = orientations[orientationId] -- If an orientation ID is specified, use a CFrame from the lookup table and then multiply it with the position CFrame.
					end
				end
				local x,y,z
				x,position = readRBXf32Array(chunk,position,instanceCount)
				y,position = readRBXf32Array(chunk,position,instanceCount)
				z,position = readRBXf32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					if values[referentIndex] then
						values[referentIndex] *= cframe(x[referentIndex],y[referentIndex],z[referentIndex])
					else
						values[referentIndex] = cframe(
							x[referentIndex],y[referentIndex],z[referentIndex],
							r00[referentIndex],r01[referentIndex],r02[referentIndex],
							r10[referentIndex],r11[referentIndex],r12[referentIndex],
							r20[referentIndex],r21[referentIndex],r22[referentIndex]
						)
					end
				end
			elseif typeId == 0x12 then -- Enum
				values,position = readu32BEArray(chunk,position,instanceCount)
			elseif typeId == 0x13 then -- Referent
				values,position = readReferentArray(chunk,position,instanceCount)
			elseif typeId == 0x14 then -- Vector3 i16
				for referentIndex = 1,instanceCount do
					local x = readu16(chunk,position) position += 2
					local y = readu16(chunk,position) position += 2
					local z = readu16(chunk,position) position += 2
					values[referentIndex] = vector3int16(x,y,z)
				end
			elseif typeId == 0x15 then -- NumberSequence
				for referentIndex = 1,instanceCount do
					local keypointCount = readu32(chunk,position) position += 4
					local keypoints = tableCreate(keypointCount)
					for i = 1,keypointCount do
						local time = readf32(chunk,position) position += 4
						local value = readf32(chunk,position) position += 4
						local envelope = readf32(chunk,position) position += 4
						keypoints[i] = numberSequenceKeypoint(time,value,envelope)
					end
					values[referentIndex] = numberSequence(keypoints)
				end
			elseif typeId == 0x16 then -- ColorSequence
				for referentIndex = 1,instanceCount do
					local keypointCount = readu32(chunk,position) position += 4
					local keypoints = tableCreate(keypointCount)
					for i = 1,keypointCount do
						local time = readf32(chunk,position) position += 4
						local r = readf32(chunk,position) position += 4
						local g = readf32(chunk,position) position += 4
						local b = readf32(chunk,position) position += 8 -- Increment by 8 instead of 4 in order to skip the envelope, which is unused.
						keypoints[i] = colorSequenceKeypoint(time,color3(r,g,b))
					end
					values[referentIndex] = colorSequence(keypoints)
				end
			elseif typeId == 0x17 then -- NumberRange
				for referentIndex = 1,instanceCount do
					local minimum = readf32(chunk,position) position += 4
					local maximum = readf32(chunk,position) position += 4
					values[referentIndex] = numberRange(minimum,maximum)
				end
			elseif typeId == 0x18 then -- Rect
				local minimumX,minimumY,maximumX,maximumY
				minimumX,position = readRBXf32Array(chunk,position,instanceCount)
				minimumY,position = readRBXf32Array(chunk,position,instanceCount)
				maximumX,position = readRBXf32Array(chunk,position,instanceCount)
				maximumY,position = readRBXf32Array(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = rect(vector2(minimumX[referentIndex],minimumY[referentIndex]),vector2(maximumX[referentIndex],maximumY[referentIndex]))
				end
			elseif typeId == 0x19 then -- PhysicalProperties
				for referentIndex = 1,instanceCount do
					local flag = readu8(chunk,position) position += 1
					if band(flag,0x01) ~= 0 then
						local density = readf32(chunk,position) position += 4
						local friction = readf32(chunk,position) position += 4
						local elasticity = readf32(chunk,position) position += 4
						local frictionWeight = readf32(chunk,position) position += 4
						local elasticityWeight = readf32(chunk,position) position += 4
						local acousticAbsorption
						if band(flag,0x02) ~= 0 then
							acousticAbsorption = readf32(chunk,position) position += 4
						end
						values[referentIndex] = physicalProperties(density,friction,elasticity,frictionWeight,elasticityWeight,acousticAbsorption)
					end
				end
			elseif typeId == 0x1A then -- Color3 u8
				for referentIndex = 1,instanceCount do
					local r = readu8(chunk,position) position += 1
					local g = readu8(chunk,position) position += 1
					local b = readu8(chunk,position) position += 1
					values[referentIndex] = color3FromRGB(r,g,b)
				end
			elseif typeId == 0x1B then -- Roblox i64
				values,position = readRBXi64Array(chunk,position,instanceCount)
			elseif typeId == 0x1C then -- Shared string
				local indices 
				indices,position = readu32BEArray(chunk,position,instanceCount)
				for referentIndex = 1,instanceCount do
					values[referentIndex] = strings[indices[referentIndex] + 1]
				end
			elseif typeId == 0x1D then -- Bytecode
				for referentIndex = 1,instanceCount do
					local bytecode 
					bytecode,position = readString(chunk,position)
					values[referentIndex] = fromstring(bytecode)
				end
			elseif typeId == 0x1F then -- UniqueId
				for referentIndex = 1,instanceCount do
					local index = readu32(chunk,position) position += 4
					local timestamp = readu32(chunk,position) position += 4
					local random
					random,position = readi64(chunk,position)
					values[referentIndex] = {
						index = index,
						timestamp = timestamp,
						random = random
					}
				end
			elseif typeId == 0x20 then -- Font
				for referentIndex = 1,instanceCount do
					local family
					family,position = readString(chunk,position)
					local weight = fontWeightFromValue(fontWeight,readu16(chunk,position)) position += 2
					local style = fontStyleFromValue(fontStyle,readu8(chunk,position)) position += 1
					local cachedFaceId
					cachedFaceId,position = readString(chunk,position)
					values[referentIndex] = font(family,weight,style)
				end
			elseif typeId == 0x22 then -- Content
				local sourceTypes
				sourceTypes,position = readRBXi32Array(chunk,position,instanceCount)
				local uriCount = readu32(chunk,position) position += 4
				local uris = tableCreate(uriCount)
				for i = 1,uriCount do
					uris[i],position = readString(chunk,position)
				end
				local objectCount = readu32(chunk,position) position += 4
				local objectReferents
				objectReferents,position = readReferentArray(chunk,position,objectCount)
				local externalCount = readu32(chunk,position) position += 4
				local externalReferents
				externalReferents,position = readReferentArray(chunk,position,objectCount)
				local uriIndex = 1
				local objectIndex = 1
				for referentIndex = 1,instanceCount do
					local sourceType = sourceTypes[referentIndex]
					if sourceType == 0 then
						values[referentIndex] = contentNone
					elseif sourceType == 1 then
						values[referentIndex] = contentFromUri(uris[uriIndex])
						uriIndex += 1
					elseif sourceType == 2 then
						values[referentIndex] = contentFromObject(referents[objectReferents[objectIndex]])
						objectIndex += 1
					end
				end
			end
			
			if optionalCFrame then
				position += 1 -- Always 0x02 (Boolean type ID)
				for referentIndex = 1,instanceCount do
					if readu8(chunk,position) == 0 then
						values[referentIndex] = nil
					end
					position += 1
				end
			end
			
			for referentIndex = 1,#referents do
				local instance = instances[referents[referentIndex]]
				instance.properties[propertyName] = values[referentIndex]
			end
		elseif chunkName == "PRNT" then
			assert(readu8(chunk,position) == 0,"unsupported PRNT version") position += 1

			local instanceCount = readu32(chunk,position) position += 4
			local childReferents,parentReferents
			childReferents,position = readReferentArray(chunk,position,instanceCount)
			parentReferents,position = readReferentArray(chunk,position,instanceCount)
			
			for referentIndex = 1,instanceCount do
				local child = instances[childReferents[referentIndex]]
				local parent = instances[parentReferents[referentIndex]]
				
				insert(parent and parent.children or instances,child)
			end
		elseif chunkName == "END\0" then
			break
		end
	end
	
	return {
		metadata = metadata,
		strings = strings,
		instances = instances,
		size = size
	}
end

return srbxm